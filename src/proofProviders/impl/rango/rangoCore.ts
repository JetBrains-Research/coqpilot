import {
    ChildProcess,
    SpawnOptionsWithStdioTuple,
    StdioNull,
    StdioPipe,
    spawn,
} from "child_process";

import { TargetType } from "../../../core/completionGenerationContext";

import { throwOnAbort } from "../../../utils/async/abortUtils";
import { PromiseExecutor, RejectType } from "../../../utils/async/promiseUtils";
import {
    buildErrorCompleteLog,
    getErrorMessage,
} from "../../../utils/errors/errorsUtils";
import { throwError } from "../../../utils/errors/throwErrors";
import { getOrCreateCoqPilotMetaLogsDir } from "../../../utils/fs/coqPilotMetaDir";
import { createDirectory } from "../../../utils/fs/directoryUtils";
import {
    addExtension,
    translateToSafeFileName,
} from "../../../utils/fs/fileNameUtils";
import {
    appendToFile,
    createFileWithParentDirectories,
    deleteFile,
    makeFileExecutable,
    readFile,
    writeToFile,
} from "../../../utils/fs/fileUtils";
import { locateExecutable } from "../../../utils/fs/lookup";
import {
    joinPaths,
    relativizeAbsolutePaths,
} from "../../../utils/fs/pathUtils";
import { createTmpDirectory } from "../../../utils/fs/tmpFs";
import { JsonSpacing, toJsonString } from "../../../utils/printers";
import { CodeElementRange } from "../../../utils/structures/codeElementPositions";
import { nowTimestampMillis } from "../../../utils/time";
import { ExternalPipelineProofGenerationContext } from "../../proofGenerationContext";
import { RangoModelParams } from "../modelParams";
import { DebugLogsWrappers } from "../proofProviderInternal";
import {
    AuxFileCreationMode,
    AuxLemma,
    withAuxFile,
} from "../utils/auxFileManager";

import {
    RangoError,
    asRangoErrorOrIllegalState,
    throwRangoError,
    throwRangoErrorWithLogs,
} from "./rangoError";
import { RangoInput } from "./rangoInput";
import {
    RangoModelSettings,
    buildRangoModelSettingsFromParams,
} from "./rangoModelSettings";

// TODO: generalize to support more external proofProviders the same way (if needed)

/**
 * Runs Rango proof generation.
 *
 * @returns A promise that resolves to the proof or `undefined` if no valid proofs were found.
 */
export async function runRangoProof(
    context: ExternalPipelineProofGenerationContext,
    params: RangoModelParams,
    rangoDirPath: string,
    clearLogsOnSuccess: boolean,
    logDebug?: DebugLogsWrappers,
    abortSignal?: AbortSignal
): Promise<string | undefined> {
    const inFileRequestUniqueIdentifier = buildInFileRequestUniqueIdentifier(
        context.completionTargetRange
    );
    /**
     * WARNING: be careful with data points possibly cached at the dataloc.
     * For the real-world case with filling "admit" - everything is safe.
     * However, when it comes to benchmarking, additional care should be taken
     * to make sure Rango does not read the original theorem (most likely, proved)
     * from the original source file - or its cached data point.
     *
     * Now this problem is solved: `AuxFileCreationMode.REUSE_SOURCE_FILE` guarantees
     * no new file is created, so Rango is expected to perform its standard way
     * to eliminate target theorem from the context.
     * However, once `AuxFileCreationMode.REUSE_SOURCE_FILE` will be no longer supported,
     * some manipulations with the original source file and its data point will be needed.
     */
    return await withAuxFile(
        {
            sourceFilePath: joinPaths(
                context.projectRootPath,
                context.relativeSourceFilePath
            ),
            targetGoal: context.completionTargetGoal,
            requestUniqueIdentifier: inFileRequestUniqueIdentifier,
            mode:
                context.targetType === TargetType.PROVE_THEOREM
                    ? AuxFileCreationMode.REUSE_SOURCE_FILE
                    : AuxFileCreationMode.INSERT_HELPER_LEMMA,
            sourceTheoremName: context.sourceTheoremName,
            sourceTheoremStatementRange: context.sourceTheoremStatementRange,
            sourceTheoremProofRange: context.sourceTheoremProofRange,
        },
        async (auxLemma) => {
            logDebug?.event("Created aux lemma", auxLemma);
            return new Promise((resolve, reject) => {
                /**
                 * Note: current pattern allows to both await the async function
                 * (needed for the async function call deep inside, namely, `locateExecutable`)
                 * and construct `Promise` with custom `{resolve, reject}` being passed further.
                 */
                (async () => {
                    try {
                        await executeRangoProofGenerationOrThrow(
                            context,
                            params,
                            rangoDirPath,
                            inFileRequestUniqueIdentifier,
                            auxLemma,
                            clearLogsOnSuccess,
                            logDebug,
                            abortSignal,
                            { resolve, reject }
                        );
                    } catch (err) {
                        reject(asRangoErrorOrIllegalState(err));
                    }
                })();
            });
        }
    );
}

async function executeRangoProofGenerationOrThrow(
    context: ExternalPipelineProofGenerationContext,
    params: RangoModelParams,
    rangoDirPath: string,
    inFileRequestUniqueIdentifier: string,
    auxLemma: AuxLemma,
    cleanLogsOnSuccess: boolean,
    logDebug: DebugLogsWrappers | undefined,
    abortSignal: AbortSignal | undefined,
    promiseExecutor: PromiseExecutor<string | undefined>
) {
    const projectPath = context.projectRootPath;
    const rangoInput: RangoInput = {
        theoremName: auxLemma.name,
        theoremRange: auxLemma.statementRange,
        proofRange: auxLemma.admittedProofRange,
        relativeSourceFilePath: relativizeAbsolutePaths(
            projectPath,
            auxLemma.auxFilePath
        ),
        projectPath: projectPath,
    };
    const modelSettings = buildRangoModelSettingsFromParams(
        params,
        rangoDirPath
    );

    throwOnAbort(abortSignal);
    const rangoFiles = prepareSharedFiles(
        rangoInput,
        modelSettings,
        buildRequestIdentifierFileName(
            params.modelId,
            context.relativeSourceFilePath,
            context.sourceTheoremName,
            inFileRequestUniqueIdentifier
        ),
        projectPath
    );
    logDebug?.event("Prepared shared files", rangoFiles);

    throwOnAbort(abortSignal);
    const rangoProcess = await spawnRangoProcess(
        rangoDirPath,
        rangoFiles,
        context,
        params,
        logDebug,
        abortSignal,
        promiseExecutor.reject
    );

    rangoProcess.on("close", (exitCode) => {
        try {
            const proof = onRangoProcessFinish(
                exitCode,
                rangoInput,
                rangoFiles,
                logDebug
            );
            if (cleanLogsOnSuccess) {
                try {
                    deleteFile(rangoFiles.logsFilePath);
                } catch (err) {}
            }
            promiseExecutor.resolve(proof);
        } catch (err) {
            promiseExecutor.reject(asRangoErrorOrIllegalState(err));
        }
    });
}

interface RangoSharedFiles {
    sharedDirPath: string;
    inputFilePath: string;
    modelSettingsFilePath: string;
    outputDirPath: string;
    logsFilePath: string;
}

function prepareSharedFiles(
    rangoInput: RangoInput,
    modelSettings: RangoModelSettings,
    rangoLogsFileName: string,
    projectPath: string
): RangoSharedFiles {
    const sharedDirPath = createDirectory(
        true,
        createTmpDirectory({ unsafeCleanup: true }),
        "coqpilot-rango-run"
    );

    const inputFilePath = joinPaths(sharedDirPath, "input.json");
    writeToFile(
        toJsonString(rangoInput, JsonSpacing.DEFAULT_FORMATTED),
        inputFilePath,
        (err) => {
            throw err;
        }
    );
    const modelSettingsFilePath = joinPaths(sharedDirPath, "settings.json");
    writeToFile(
        toJsonString(modelSettings, JsonSpacing.DEFAULT_FORMATTED),
        modelSettingsFilePath,
        (err) => {
            throw err;
        }
    );

    const outputDirPath = createDirectory(true, sharedDirPath, "output");

    const logsFilePath = createFileWithParentDirectories(
        "throw",
        joinPaths(
            getOrCreateCoqPilotMetaLogsDir(projectPath),
            rangoLogsFileName
        )
    );

    return {
        sharedDirPath: sharedDirPath,
        inputFilePath: inputFilePath,
        modelSettingsFilePath: modelSettingsFilePath,
        outputDirPath: outputDirPath,
        logsFilePath: logsFilePath,
    };
}

async function spawnRangoProcess(
    rangoDirPath: string,
    rangoFiles: RangoSharedFiles,
    context: ExternalPipelineProofGenerationContext,
    params: RangoModelParams,
    logDebug: DebugLogsWrappers | undefined,
    abortSignal: AbortSignal | undefined,
    reject: RejectType
): Promise<ChildProcess> {
    const executionScriptPath = createExecutionScript(rangoDirPath, rangoFiles);
    const scriptExecutable = await wrapExecutionScriptIntoExecutable(
        executionScriptPath,
        context.requiresNixEnvironment
    );

    const spawnOptions: SpawnOptionsWithStdioTuple<
        StdioNull,
        StdioPipe,
        StdioPipe
    > = {
        cwd: context.projectRootPath,
        stdio: ["ignore", "pipe", "pipe"],
        env: {
            ...process.env,
            OPENAI_API_KEY: params.mockOpenAIApiKey,
            OPENAI_ORG_KEY: "",
        },
        shell: true,
        signal: abortSignal,
    };
    const childProccess = spawn(scriptExecutable, [], spawnOptions);

    // Set up logs
    function appendRangoLogs(data: any) {
        appendToFile(data.toString(), rangoFiles.logsFilePath, (err) =>
            console.error(
                `Failed to append logs from Rango child process: ${buildErrorCompleteLog(err)}`
            )
        );
    }
    childProccess.stdout.on("data", appendRangoLogs);
    childProccess.stderr.on("data", appendRangoLogs);

    // Catch spawn (like "file not found") and abort errors
    childProccess.on("error", (err) => {
        // TODO: throw proper `AbortError` here and handle it at the top-level
        const errorMessage =
            err.name === "AbortError"
                ? "Rango subprocess has been aborted"
                : `Failed to launch Rango subprocess: ${getErrorMessage(err)}`;
        reject(new RangoError(errorMessage, rangoFiles.logsFilePath));
    });

    logDebug?.event("Spawned Rango subprocess", {
        executionScriptPath: executionScriptPath,
        options: spawnOptions,
    });

    return childProccess;
}

function onRangoProcessFinish(
    exitCode: number | null,
    rangoInput: RangoInput,
    rangoFiles: RangoSharedFiles,
    logDebug: DebugLogsWrappers | undefined
): string | undefined {
    logDebug?.event(`Subprocess finished with exit code ${exitCode}`);

    if (exitCode !== 0) {
        throwRangoErrorWithLogs(
            rangoFiles.logsFilePath,
            `Rango process failed: exit code ${exitCode}`
        );
    }

    const startPostion = rangoInput.theoremRange.start;
    const outputFileName = `${startPostion.line}-${startPostion.character}.json`;
    const outputContent = readFile(
        joinPaths(
            rangoFiles.outputDirPath,
            "target_project",
            rangoInput.relativeSourceFilePath,
            outputFileName
        ),
        (err) =>
            throwRangoErrorWithLogs(
                rangoFiles.logsFilePath,
                "Rango process has successfully finished, ",
                `but its output file could not be read: ${getErrorMessage(err)}`
            )
    );
    try {
        const proof = JSON.parse(outputContent).proof;
        if (proof === undefined) {
            throwError("`proof` is not found in the resulting JSON");
        }
        if (proof === null) {
            return undefined; // Rango's proof search failed
        } else {
            return proof as string;
        }
    } catch (err) {
        throwRangoErrorWithLogs(
            rangoFiles.logsFilePath,
            `Failed to parse Rango's output file: ${getErrorMessage(err)}`
        );
    }
}

function buildInFileRequestUniqueIdentifier(
    completionTargetRange: CodeElementRange
): string {
    const startPosition = completionTargetRange.start;
    return `${startPosition.line}_${startPosition.character}`;
}

function buildRequestIdentifierFileName(
    modelId: string,
    relativeSourceFilePath: string,
    theoremName: string,
    inFileRequestUniqueIdentifier: string
) {
    const unsafeFileName = [
        `rango-run-${modelId}-${relativeSourceFilePath}-`,
        `${theoremName}-${inFileRequestUniqueIdentifier}-${nowTimestampMillis()}`,
    ].join("");
    return addExtension(translateToSafeFileName(unsafeFileName), ".txt");
}

const RANGO_PYTHON_VERSION = "3.11";

function createExecutionScript(
    rangoDirPath: string,
    rangoFiles: RangoSharedFiles
): string {
    const pythonArgs = [
        getRangoAdapterScriptPath(rangoDirPath),
        `--rango_dir=${rangoDirPath}`,
        `--target=${rangoFiles.inputFilePath}`,
        `--settings=${rangoFiles.modelSettingsFilePath}`,
        `--output_dir=${rangoFiles.outputDirPath}`,
    ];
    const executionScriptCode = [
        "#!/usr/bin/env bash",
        "set -e",
        "",
        'echo "[Execution script] Starting subprocess execution..."',
        "",
        `cd "${rangoDirPath}"`,
        "",
        'export PYENV_ROOT="$HOME/.pyenv"',
        'export PATH="$PYENV_ROOT/bin:$PATH"',
        'eval "$(pyenv init -)"',
        `pyenv shell ${RANGO_PYTHON_VERSION}`,
        "",
        'echo "[Execution script] Set up pyenv, Python version: $(python --version)"',
        "",
        'echo "[Execution script] Entering Python virutal environment..."',
        `${getPythonVenvEnterShellCommand()}`,
        "",
        'echo "[Execution script] Executing Python script..."',
        `exec python3 ${pythonArgs.join(" ")}`,
    ].join("\n");

    try {
        const executionScriptPath = createFileWithParentDirectories(
            "throw",
            joinPaths(rangoFiles.sharedDirPath, "execution-script.sh")
        );
        writeToFile(executionScriptCode, executionScriptPath, (err) => {
            throw err;
        });
        makeFileExecutable(executionScriptPath);
        return executionScriptPath;
    } catch (err) {
        throwRangoError(
            `Failed to create execution script: ${getErrorMessage(err)}`
        );
    }
}

async function wrapExecutionScriptIntoExecutable(
    executionScriptPath: string,
    requiresNixEnvironment: boolean
): Promise<string> {
    if (!requiresNixEnvironment) {
        return executionScriptPath;
    }
    const nixShell = await locateExecutable("nix-shell");
    if (nixShell === undefined) {
        throwRangoError(
            "Failed to locate `nix-shell` required to spawn Rango subprocess ",
            "in the Nix environment, which is used by the target Coq project. ",
            "Check `nix-shell` is accessible and try again."
        );
    }
    return `${nixShell} --run "${executionScriptPath}"`;
}

function getPythonVenvEnterShellCommand(): string {
    if (process.platform === "win32") {
        throwRangoError(
            "Windows platform is currently unsupported for proof-generation with Rango"
        );
    }
    const activationScript = "./venv/bin/activate";
    return `source ${activationScript}`;
}

function getRangoAdapterScriptPath(rangoDirPath: string): string {
    return joinPaths(rangoDirPath, "scripts", "generate_proof.py");
}
