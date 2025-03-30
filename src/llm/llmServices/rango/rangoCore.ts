import {
    ChildProcess,
    SpawnOptionsWithStdioTuple,
    StdioNull,
    StdioPipe,
    spawn,
} from "child_process";
import * as tmp from "tmp";

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
    copyFile,
    createFileWithParentDirectories,
    readFile,
    writeToFile,
} from "../../../utils/fs/fileUtils";
import {
    joinPaths,
    relativizeAbsolutePaths,
} from "../../../utils/fs/pathUtils";
import { JsonSpacing, toJsonString } from "../../../utils/printers";
import { CodeElementRange } from "../../../utils/structures/codeElementPositions";
import { nowTimestampMillis } from "../../../utils/time";
import { ExternalPipelineProofGenerationContext } from "../../proofGenerationContext";
import { DebugLogsWrappers } from "../llmServiceInternal";
import { MockRangoModelParams } from "../modelParams";
import { AuxLemma, withAuxFile } from "../utils/auxFileManager";

import { RangoInput } from "./rangoInput";

/**
 * Runs Rango proof generation.
 *
 * @returns A promise that resolves to the proof or `undefined` if no valid proofs were found.
 */
export async function runRangoProof(
    context: ExternalPipelineProofGenerationContext,
    params: MockRangoModelParams,
    rangoDirPath: string,
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
                        logDebug,
                        abortSignal,
                        { resolve: resolve, reject: reject }
                    );
                } catch (err) {
                    reject(err);
                }
            });
        }
    );
}

function executeRangoProofGenerationOrThrow(
    context: ExternalPipelineProofGenerationContext,
    params: MockRangoModelParams,
    rangoDirPath: string,
    inFileRequestUniqueIdentifier: string,
    auxLemma: AuxLemma,
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

    throwOnAbort(abortSignal);
    const rangoFiles = prepareSharedFiles(
        rangoInput,
        buildRequestIdentifierFileName(
            params.modelId,
            context.relativeSourceFilePath,
            context.sourceTheoremName,
            inFileRequestUniqueIdentifier
        )
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
                projectPath,
                rangoInput,
                rangoFiles,
                logDebug
            );
            promiseExecutor.resolve(proof);
        } catch (err) {
            promiseExecutor.reject(err);
        }
    });
}

interface RangoSharedFiles {
    inputFilePath: string;
    outputDirPath: string;
    logsFilePath: string;
}

function prepareSharedFiles(
    rangoInput: RangoInput,
    rangoLogsFileName: string
): RangoSharedFiles {
    const sharedDirPath = createDirectory(
        true,
        tmp.dirSync({ unsafeCleanup: true }).name,
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
    const outputDirPath = createDirectory(true, sharedDirPath, "output");
    const logsFilePath = createFileWithParentDirectories(
        "throw",
        joinPaths(sharedDirPath, rangoLogsFileName)
    );
    return {
        inputFilePath: inputFilePath,
        outputDirPath: outputDirPath,
        logsFilePath: logsFilePath,
    };
}

function spawnRangoProcess(
    rangoDirPath: string,
    rangoFiles: RangoSharedFiles,
    params: MockRangoModelParams,
    logDebug: DebugLogsWrappers | undefined,
    abortSignal: AbortSignal | undefined,
    reject: RejectType
): ChildProcess {
    const pythonExecutable = getPythonExecutableCommand(rangoDirPath);
    const pythonArgs = [
        getRangoAdapterScriptPath(rangoDirPath),
        `--rango_dir=${rangoDirPath}`,
        `--target=${rangoFiles.inputFilePath}`,
        `--output_dir=${rangoFiles.outputDirPath}`,
    ];

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
            COQPILOT_RANGO_TIMEOUT_PARAMETER: params.timeoutSeconds.toString(),
            OPENAI_API_KEY: params.openAiApiKey,
            OPENAI_ORG_KEY: "",
        },
        shell: true,
        signal: abortSignal,
    };
    const childProccess = spawn(pythonExecutable, pythonArgs, spawnOptions);

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

    // Catch spawn errors (like "file not found")
    childProccess.on("error", (err) => {
        reject(
            new Error(
                `Failed to launch Rango subprocess: ${getErrorMessage(err)}`
            )
        );
    });

    logDebug?.event("Spawned Rango subprocess", {
        executable: pythonExecutable,
        args: pythonArgs,
        options: spawnOptions,
    });

    return childProccess;
}

function onRangoProcessFinish(
    exitCode: number | null,
    projectPath: string,
    rangoInput: RangoInput,
    rangoFiles: RangoSharedFiles,
    logDebug: DebugLogsWrappers | undefined
): string | undefined {
    logDebug?.event(`Subprocess finished with exit code ${exitCode}`);
    if (exitCode !== 0) {
        // TODO: support option to save logs even in case of success (?)
        const userLogsFilePath = copyFile(
            rangoFiles.logsFilePath,
            getOrCreateCoqPilotMetaLogsDir(projectPath),
            true
        );
        throwError(
            `Rango process failed (exit code ${exitCode}): `,
            `logs are available at ${userLogsFilePath}`
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
            throwError(
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
        throwError(
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

function getPythonExecutableCommand(rangoDirPath: string): string {
    const pyenvShellSetupCommands = [
        'export PYENV_ROOT="$HOME/.pyenv"',
        'export PATH="$PYENV_ROOT/bin:$PATH"',
        'eval "$(pyenv init -)"',
    ].join(" && ");
    const pyenvEnterShellCommand = `pyenv shell ${RANGO_PYTHON_VERSION}`;
    const pythonVenvExecutable = getPythonVenvExecutablePath(rangoDirPath);
    return `${pyenvShellSetupCommands} && ${pyenvEnterShellCommand} && ${pythonVenvExecutable}`;
}

function getPythonVenvExecutablePath(rangoDirPath: string): string {
    if (process.platform === "win32") {
        // to support Windows here: joinPaths(rangoDir, "venv", "Scripts", "python.exe")
        throwError(
            "Windows platform is currently unsupported for proof-generation with Rango"
        );
    }
    return joinPaths(rangoDirPath, "venv", "bin", "python");
}

function getRangoAdapterScriptPath(rangoDirPath: string): string {
    return joinPaths(rangoDirPath, "scripts", "generate_proof.py");
}
