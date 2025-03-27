import { ChildProcess, spawn } from "child_process";
import * as tmp from "tmp";

import { CodeElementRange } from "../../../utils/codeElementPositions";
import {
    buildErrorCompleteLog,
    getErrorMessage,
} from "../../../utils/errorsUtils";
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
import { PromiseExecutor, RejectType } from "../../../utils/promiseUtils";
import { throwError } from "../../../utils/throwErrors";
import { nowTimestampMillis } from "../../../utils/time";
import { ExternalPipelineProofGenerationContext } from "../../proofGenerationContext";
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
    rangoDirPath: string
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
            return new Promise((resolve, reject) => {
                try {
                    executeRangoProofGenerationOrThrow(
                        context,
                        params,
                        rangoDirPath,
                        inFileRequestUniqueIdentifier,
                        auxLemma,
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

    const rangoFiles = prepareSharedFiles(
        rangoInput,
        buildRequestIdentifierFileName(
            params.modelId,
            context.relativeSourceFilePath,
            context.sourceTheoremName,
            inFileRequestUniqueIdentifier
        )
    );

    const rangoProcess = spawnRangoProcess(
        rangoDirPath,
        rangoFiles,
        params,
        promiseExecutor.reject
    );

    rangoProcess.on("close", (exitCode) => {
        try {
            const proof = onRangoProcessFinish(
                exitCode,
                projectPath,
                rangoInput,
                rangoFiles
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
    reject: RejectType
): ChildProcess {
    const pythonExecutable = getPythonVenvExecutablePath(rangoDirPath);
    const pythonArgs = [
        getRangoAdapterScriptPath(rangoDirPath),
        `--rango_dir=${rangoDirPath}`,
        `--target=${rangoFiles.inputFilePath}`,
        `--output_dir=${rangoFiles.outputDirPath}`,
    ];

    // TODO (!): support nix
    const childProccess = spawn(pythonExecutable, pythonArgs, {
        cwd: rangoDirPath,
        stdio: ["ignore", "pipe", "pipe"],
        env: {
            ...process.env,
            COQPILOT_RANGO_TIMEOUT_PARAMETER: params.timeoutSeconds.toString(),
            OPENAI_API_KEY: params.openAiApiKey,
            OPENAI_ORG_KEY: "",
        },
    });

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

    return childProccess;
}

function onRangoProcessFinish(
    exitCode: number | null,
    projectPath: string,
    rangoInput: RangoInput,
    rangoFiles: RangoSharedFiles
): string | undefined {
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
