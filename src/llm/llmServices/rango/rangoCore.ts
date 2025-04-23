import {
    ChildProcess,
    SpawnOptionsWithStdioTuple,
    StdioNull,
    StdioPipe,
    spawn,
} from "child_process";

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
import {
    joinPaths,
    relativizeAbsolutePaths,
} from "../../../utils/fs/pathUtils";
import { createTmpDirectory } from "../../../utils/fs/tmpFs";
import { JsonSpacing, toJsonString } from "../../../utils/printers";
import { CodeElementRange } from "../../../utils/structures/codeElementPositions";
import { nowTimestampMillis } from "../../../utils/time";
import { ExternalPipelineProofGenerationContext } from "../../proofGenerationContext";
import { DebugLogsWrappers } from "../llmServiceInternal";
import { RangoModelParams } from "../modelParams";
import { AuxLemma, withAuxFile } from "../utils/auxFileManager";

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
    return await withAuxFile(
        {
            sourceFilePath: joinPaths(
                context.projectRootPath,
                context.relativeSourceFilePath
            ),
            targetGoal: context.completionTargetGoal,
            lineToCopyFileToExclusive: context.sourceTheoremStartLine,
            requestUniqueIdentifier: inFileRequestUniqueIdentifier,
        },
        async (auxLemma) => {
            logDebug?.event("Created aux lemma", auxLemma);
            return new Promise((resolve, reject) => {
                try {
                    executeRangoProofGenerationOrThrow(
                        context,
                        params,
                        rangoDirPath,
                        inFileRequestUniqueIdentifier,
                        auxLemma,
                        clearLogsOnSuccess,
                        logDebug,
                        abortSignal,
                        { resolve: resolve, reject: reject }
                    );
                } catch (err) {
                    reject(asRangoErrorOrIllegalState(err));
                }
            });
        }
    );
}

function executeRangoProofGenerationOrThrow(
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
    const rangoProcess = spawnRangoProcess(
        rangoDirPath,
        rangoFiles,
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

function spawnRangoProcess(
    rangoDirPath: string,
    rangoFiles: RangoSharedFiles,
    params: RangoModelParams,
    logDebug: DebugLogsWrappers | undefined,
    abortSignal: AbortSignal | undefined,
    reject: RejectType
): ChildProcess {
    const executionScriptPath = createExecutionScript(rangoDirPath, rangoFiles);

    // TODO (!): support nix
    const spawnOptions: SpawnOptionsWithStdioTuple<
        StdioNull,
        StdioPipe,
        StdioPipe
    > = {
        cwd: rangoDirPath,
        stdio: ["ignore", "pipe", "pipe"],
        env: {
            ...process.env,
            OPENAI_API_KEY: params.mockOpenAIApiKey,
            OPENAI_ORG_KEY: "",
        },
        shell: true,
        signal: abortSignal,
    };
    const childProccess = spawn(executionScriptPath, [], spawnOptions);

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
