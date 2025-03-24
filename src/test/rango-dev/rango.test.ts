import { ChildProcess, spawn } from "child_process";
import * as tmp from "tmp";

import {
    AuxLemma,
    withAuxFile,
} from "../../llm/llmServices/utils/auxFileManager";

import { ProofGoal } from "../../coqLsp/coqLspTypes";

import {
    buildErrorCompleteLog,
    getErrorMessage,
} from "../../utils/errorsUtils";
import { getOrCreateCoqPilotMetaLogsDir } from "../../utils/fs/coqPilotMetaDir";
import { createDirectory } from "../../utils/fs/directoryUtils";
import {
    addExtension,
    translateToSafeFileName,
} from "../../utils/fs/fileNameUtils";
import {
    createFileWithParentDirectories,
    readFile,
} from "../../utils/fs/fileUtils";
import { appendToFile, copyFile, writeToFile } from "../../utils/fs/fileUtils";
import { joinPaths, relativizeAbsolutePaths } from "../../utils/fs/pathUtils";
import { JsonSpacing, toJsonString } from "../../utils/printers";
import { PromiseExecutor, RejectType } from "../../utils/promiseUtils";
import { throwError } from "../../utils/throwErrors";
import { nowTimestampMillis } from "../../utils/time";
import { parseTheoremsFromCoqFile } from "../commonTestFunctions/coqFileParser";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

import { RangoInput } from "./structs";

suite("[SourceExecutable] Rango", () => {
    const rangoDirPath = "/Users/Gleb.Solovev/coqpilot-rango-fork";
    const target: RangoInput = {
        theoremName: "test_admitted",
        theoremRange: {
            start: {
                line: 2,
                character: 0,
            },
            end: {
                line: 2,
                character: 69,
            },
        },
        proofRange: {
            start: {
                line: 3,
                character: 0,
            },
            end: {
                line: 5,
                character: 9,
            },
        },
        relativeSourceFilePath: "theories/C.v",
        projectPath: resolveResourcesDir(["coqProj"])[0],
    };

    test("Run test rango", async () => {
        const theorems = await parseTheoremsFromCoqFile(
            ["coqProj", "theories", "C.v"],
            ["coqProj"]
        );
        const proof = await runRangoProof(
            "rango-model",
            rangoDirPath,
            theorems[0].initial_goal!,
            target,
            "4_0"
        );
        console.error(`\n\nRango result:\n${proof}\n\n`);
    }).timeout(60_000);
});

/**
 * Runs Rango proof generation.
 *
 * @returns A promise that resolves to the proof or `undefined` if no valid proofs were found.
 */
export async function runRangoProof(
    modelId: string,
    rangoDirPath: string,
    targetGoal: ProofGoal,
    inputData: RangoInput,
    inFileRequestUniqueIdentifier: string // TODO: build from the target admit position
): Promise<string | undefined> {
    return await withAuxFile(
        {
            sourceFilePath: joinPaths(
                inputData.projectPath,
                inputData.relativeSourceFilePath
            ),
            targetGoal: targetGoal,
            lineToCopyFileToExclusive: inputData.theoremRange.start.line,
            requestUniqueIdentifier: inFileRequestUniqueIdentifier,
        },
        async (auxLemma) => {
            return new Promise((resolve, reject) => {
                try {
                    executeRangoProofGenerationOrThrow(
                        modelId,
                        rangoDirPath,
                        inputData,
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
    modelId: string,
    rangoDirPath: string,
    inputData: RangoInput,
    inFileRequestUniqueIdentifier: string,
    auxLemma: AuxLemma,
    promiseExecutor: PromiseExecutor<string | undefined>
) {
    const projectPath = inputData.projectPath;
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
            modelId,
            inputData.relativeSourceFilePath,
            inputData.theoremName,
            inFileRequestUniqueIdentifier
        )
    );

    const rangoProcess = spawnRangoProcess(
        rangoDirPath,
        rangoFiles,
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
    reject: RejectType
): ChildProcess {
    const pythonExecutable = getPythonVenvExecutablePath(rangoDirPath);
    const pythonArgs = [
        getRangoAdapterScriptPath(rangoDirPath),
        `--rango_dir=${rangoDirPath}`,
        `--target=${rangoFiles.inputFilePath}`,
        `--output_dir=${rangoFiles.outputDirPath}`,
    ];

    // TODO: support nix
    const childProccess = spawn(pythonExecutable, pythonArgs, {
        cwd: rangoDirPath,
        stdio: ["ignore", "pipe", "pipe"],
        env: {
            ...process.env,
            // OPENAI_API_KEY, // TODO: pass through the model params
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
        // joinPaths(rangoDir, "venv", "Scripts", "python.exe")
        throwError(
            "Windows platform is currently unsupported for proof-generation with Rango"
        );
    }
    return joinPaths(rangoDirPath, "venv", "bin", "python");
}

function getRangoAdapterScriptPath(rangoDirPath: string): string {
    return joinPaths(rangoDirPath, "scripts", "generate_proof.py");
}
