import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { Goal, PpString } from "../../../../coqLsp/coqLspTypes";

import { resolveOrThrow } from "../../../commonTestFunctions/resolveOrThrow";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingModelParams";
import {
    CompletionGenerationTask,
    TargetType,
    WorkspaceRoot,
} from "../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { ParsedCoqFileData } from "../structures/parsedCoqFileData";
import { TheoremData } from "../structures/theoremData";
import { CodeElementRange } from "../structures/utilStructures";
import { buildAndParseCoqProjectInSubprocess } from "../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { getParamsResolver, getShortName } from "../utils/llmServicesUtils";
import { resolveTheoremsRanker } from "../utils/resolveTheoremsRanker";
import { SubprocessesScheduler } from "../utils/subprocessUtils/subprocessesScheduler";

import { InputBenchmarkingBundle } from "./experiment";
import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { FilePathToFileTarget, InputTargets } from "./targetsBuilder";

/**
 * Builds and parses requested Coq projects via subprocesses, then constructs benchmarking items.
 */
export async function buildBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>[],
    mergedInputTargets: InputTargets | undefined,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<BenchmarkingItem[]> {
    const workspaceToParsedFiles = await buildAndParseRequestedCoqProjects(
        mergedInputTargets,
        runOptions,
        subprocessesScheduler,
        logger
    );
    const benchmarkingItems = constructBenchmarkingItems(
        inputBundles,
        workspaceToParsedFiles
    );
    logger
        .asOneRecord()
        .info(
            `successfully constructed ${benchmarkingItems.length} benchmarking items`,
            undefined,
            ""
        )
        .debug(`:\n${logBenchmarkingItems(benchmarkingItems)}`);
    return benchmarkingItems;
}

function logBenchmarkingItems(benchmarkingItems: BenchmarkingItem[]): string {
    const benchmarkingItemsLogs = [];
    for (let i = 0; i < benchmarkingItems.length; i++) {
        benchmarkingItemsLogs.push(
            `\tbenchmarking item ${i}:\n${logBenchmarkingItem(benchmarkingItems[i])}`
        );
    }
    return benchmarkingItemsLogs.join("\n---\n");
}

function logBenchmarkingItem(benchmarkingItem: BenchmarkingItem): string {
    const task = benchmarkingItem.task;
    const targetLog = `* target: ${getTargetTypeName(task.targetType)}, goal ${task.targetGoalToProveAsString}`;
    const sourceLog = `* source: ${task.targetPositionRange} of theorem "${task.sourceTheorem.name}" from "${task.sourceFilePath}"`;
    const paramsLog = `* model id: "${benchmarkingItem.params.modelParams.modelId}"`; // TODO: support theorem ranker name
    const llmServiceLog = `* LLM service: ${getShortName(benchmarkingItem.llmServiceIdentifier)}`;
    return `${targetLog}\n${sourceLog}\n${paramsLog}\n${llmServiceLog}`;
}

function getTargetTypeName(targetType: TargetType): string {
    switch (targetType) {
        case TargetType.ADMIT:
            return "complete hole";
        case TargetType.PROVE_THEOREM:
            return "prove theorem";
    }
}

type WorkspaceToParsedFiles = Map<
    WorkspaceRoot | undefined,
    FilePathToParsedData
>;

type FilePathToParsedData = Map<string, ParsedCoqFileData>;

/**
 * @returns requested source file paths mapped to their parsed data.
 */
async function buildAndParseRequestedCoqProjects(
    inputTargets: InputTargets | undefined,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<WorkspaceToParsedFiles> {
    if (inputTargets === undefined) {
        throw Error(
            "`inputTargets` should be built before building and parsing requested projects"
        );
    }
    const workspaceToParsedFiles: WorkspaceToParsedFiles = new Map();
    for (const [
        workspaceRoot,
        filePathToFileTargets,
    ] of inputTargets.entries()) {
        const parsedFiles = await buildAndParseCoqProjectOrThrow(
            workspaceRoot,
            filePathToFileTargets,
            runOptions,
            subprocessesScheduler,
            logger
        );
        workspaceToParsedFiles.set(
            workspaceRoot,
            new Map(
                parsedFiles.map((parsedFile) => [
                    parsedFile.filePath,
                    parsedFile,
                ])
            )
        );
    }
    logger.info("successfully built and parsed requested Coq projects");
    return workspaceToParsedFiles;
}

async function buildAndParseCoqProjectOrThrow(
    workspaceRoot: WorkspaceRoot | undefined,
    filePathToFileTargets: FilePathToFileTarget,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<ParsedCoqFileData[]> {
    const requestedFilesToParsePaths = Array.from(filePathToFileTargets.keys());
    const executionResult = await buildAndParseCoqProjectInSubprocess(
        workspaceRoot,
        requestedFilesToParsePaths,
        true, // TODO: support turning projects rebuilding off
        runOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
        subprocessesScheduler,
        logger,
        runOptions.enableSubprocessLifetimeDebugLogs
    );
    const projectId =
        workspaceRoot === undefined
            ? "standalone source files requested"
            : `"${workspaceRoot}" project with source files requested`;
    if (executionResult.isFailed()) {
        logger
            .asOneRecord()
            .error(`failed to build and parse ${projectId}`, undefined, "")
            .debug(`: ${requestedFilesToParsePaths.join(", ")}`, undefined, "")
            .error(
                `\n\tcaused by \`${executionResult.errorTypeName}\`: ${executionResult.errorMessage}`
            );
        throw Error("failed to build benchmarking items");
    }
    const parsedCoqFilesData = executionResult.maybeResult!;
    logger.info(
        `successfully built and parsed ${projectId}: ${parsedCoqFilesData.length} parsed files`
    );
    return parsedCoqFilesData;
}

function constructBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>[],
    workspaceToParsedFiles: WorkspaceToParsedFiles
): BenchmarkingItem[] {
    const benchmarkingItems: BenchmarkingItem[] = [];
    for (const inputBundle of inputBundles) {
        const bundleTasks = constructTasksForBundleTargets(
            inputBundle.targets,
            workspaceToParsedFiles
        );
        for (const inputParams of inputBundle.inputBenchmarkingModelsParams) {
            bundleTasks.forEach((task) =>
                benchmarkingItems.push({
                    task: task,
                    params: resolveInputBenchmarkingModelParams(
                        inputParams,
                        inputBundle.llmServiceIdentifier
                    ),
                    llmServiceIdentifier: inputBundle.llmServiceIdentifier,
                })
            );
        }
    }
    // TODO: make items unique (!)
    return benchmarkingItems;
}

function resolveInputBenchmarkingModelParams(
    inputParams: InputBenchmarkingModelParams.Params,
    llmServiceIdentifier: LLMServiceIdentifier
): BenchmarkingModelParams<ModelParams> {
    const paramsResolver = getParamsResolver(llmServiceIdentifier);
    const { ranker, ...pureInputModelParams } = inputParams;
    return {
        theoremRanker: resolveTheoremsRanker(inputParams.ranker),
        modelParams: resolveOrThrow(paramsResolver, pureInputModelParams),
    };
}

interface TaskTarget {
    targetGoalToProve: Goal<PpString>;
    targetPositionRange: CodeElementRange;
}

function constructTasksForBundleTargets(
    bundleTargets: InputTargets,
    workspaceToParsedFiles: WorkspaceToParsedFiles
): CompletionGenerationTask[] {
    const tasks: CompletionGenerationTask[] = [];
    for (const [
        workspaceRoot,
        filePathToFileTargets,
    ] of bundleTargets.entries()) {
        const parsedFiles = workspaceToParsedFiles.get(workspaceRoot);
        if (parsedFiles === undefined) {
            throw Error(
                `no parsed files data found for requested workspace root: "${workspaceRoot?.directoryPath}"`
            );
        }
        for (const [filePath, fileTarget] of filePathToFileTargets.entries()) {
            const parsedFileData = parsedFiles.get(filePath);
            if (parsedFileData === undefined) {
                throw Error(
                    `no parsed file data found for requested source file: "${filePath}"`
                );
            }

            // construct all theorems targets
            const targetTypesForAllTheorems = [];
            if (fileTarget.allTheoremsAsAdmitTargets) {
                targetTypesForAllTheorems.push(TargetType.ADMIT);
            }
            if (fileTarget.allTheoremsAsProveTheoremTargets) {
                targetTypesForAllTheorems.push(TargetType.PROVE_THEOREM);
            }
            targetTypesForAllTheorems.forEach((targetType) => {
                for (const theorem of parsedFileData.allFileTheorems) {
                    extractTaskTargetsFromTheorem(theorem, targetType).forEach(
                        (taskTarget) =>
                            tasks.push(
                                new CompletionGenerationTask(
                                    taskTarget.targetGoalToProve,
                                    taskTarget.targetPositionRange,
                                    targetType,
                                    parsedFileData,
                                    theorem,
                                    workspaceRoot
                                )
                            )
                    );
                }
            });

            // construct specific theorems targets
            const theoremNameToData = new Map(
                parsedFileData.allFileTheorems.map((theoremData) => [
                    theoremData.name,
                    theoremData,
                ])
            );
            for (const [
                theoremName,
                theoremTarget,
            ] of fileTarget.specificTheoremTargets) {
                const targetTypes = [];
                if (
                    theoremTarget.admitTargets &&
                    !fileTarget.allTheoremsAsAdmitTargets
                ) {
                    targetTypes.push(TargetType.ADMIT);
                }
                if (
                    theoremTarget.proveTheoremTarget &&
                    !fileTarget.allTheoremsAsProveTheoremTargets
                ) {
                    targetTypes.push(TargetType.PROVE_THEOREM);
                }
                const theorem = theoremNameToData.get(theoremName);
                if (theorem === undefined) {
                    throw Error(
                        `no parsed theorem data for requested theorem "${theoremName}" of "${filePath}" file`
                    );
                }
                targetTypes.forEach((targetType) => {
                    extractTaskTargetsFromTheorem(theorem, targetType).forEach(
                        (taskTarget) =>
                            tasks.push(
                                new CompletionGenerationTask(
                                    taskTarget.targetGoalToProve,
                                    taskTarget.targetPositionRange,
                                    targetType,
                                    parsedFileData,
                                    theorem,
                                    workspaceRoot
                                )
                            )
                    );
                });
            }
        }
    }
    return tasks;
}

function extractTaskTargetsFromTheorem(
    theorem: TheoremData,
    targetType: TargetType
): TaskTarget[] {
    switch (targetType) {
        case TargetType.ADMIT:
            return theorem.proof!.holes.map((holeProofStep) => {
                return {
                    targetGoalToProve: undefined, // TODO: request to coq lsp is needed for this x_x
                    targetPositionRange: holeProofStep.range,
                };
            });
        case TargetType.PROVE_THEOREM:
            const firstProofStep = theorem.proof!.proof_steps[1];
            return [
                {
                    targetGoalToProve: undefined, // TODO: request to coq lsp is needed for this x_x
                    targetPositionRange: firstProofStep.range,
                },
            ];
    }
}
