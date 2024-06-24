import { ModelParams } from "../../../../llm/llmServices/modelParams";

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
import { buildAndParseCoqProjectInSubprocess } from "../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";
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
    mergedInputTargets: InputTargets,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<BenchmarkingItem[]> {
    const workspaceToParsedFileTargets =
        await buildAndParseRequestedCoqProjects(
            mergedInputTargets,
            runOptions,
            subprocessesScheduler,
            logger
        );
    const benchmarkingItems = constructBenchmarkingItems(
        inputBundles,
        workspaceToParsedFileTargets
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
    const llmServiceLog = `* LLM service: ${getShortName(benchmarkingItem.params.llmServiceIdentifier)}`;
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

type ParsedFileTargets =
    BuildAndParseCoqProjectBySubprocessSignature.UnpackedResultModels.UnpackedResult;

type WorkspaceToParsedFileTargets = Map<
    WorkspaceRoot | undefined,
    ParsedFileTargets
>;

async function buildAndParseRequestedCoqProjects(
    inputTargets: InputTargets,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<WorkspaceToParsedFileTargets> {
    const workspaceToParsedFileTargets: WorkspaceToParsedFileTargets =
        new Map();
    for (const [
        workspaceRoot,
        filePathToFileTargets,
    ] of inputTargets.entries()) {
        const parsedFileTargets = await buildAndParseCoqProjectOrThrow(
            workspaceRoot,
            filePathToFileTargets,
            runOptions,
            subprocessesScheduler,
            logger
        );
        workspaceToParsedFileTargets.set(workspaceRoot, parsedFileTargets);
    }
    logger.info("successfully built and parsed requested Coq projects");
    return workspaceToParsedFileTargets;
}

async function buildAndParseCoqProjectOrThrow(
    workspaceRoot: WorkspaceRoot | undefined,
    sourceFileTargetsToParse: FilePathToFileTarget,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<ParsedFileTargets> {
    const executionResult = await buildAndParseCoqProjectInSubprocess(
        workspaceRoot,
        sourceFileTargetsToParse,
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
            .debug(
                `: ${Array.from(sourceFileTargetsToParse.keys()).join(", ")}`,
                undefined,
                ""
            )
            .error(
                `\n\tcaused by \`${executionResult.errorTypeName}\`: ${executionResult.errorMessage}`
            );
        throw Error("failed to build benchmarking items");
    }
    const parsedFileTargets = executionResult.maybeResult!;
    logger.info(
        `successfully built and parsed ${projectId}: ${parsedFileTargets.size} parsed files`
    );
    return parsedFileTargets;
}

function constructBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle<InputBenchmarkingModelParams.Params>[],
    workspaceToParsedFileTargets: WorkspaceToParsedFileTargets
): BenchmarkingItem[] {
    const modelIdToAllRequestedTasks: Map<string, CompletionGenerationTask[]> =
        new Map();
    const modelIdToResolvedParams: Map<
        string,
        BenchmarkingModelParams<ModelParams>
    > = new Map();
    for (const inputBundle of inputBundles) {
        const bundleTasks = constructTasksForBundleTargets(
            inputBundle.targets,
            workspaceToParsedFileTargets
        ) as CompletionGenerationTask[];
        for (const inputParams of inputBundle.inputBenchmarkingModelsParams) {
            const modelId = inputParams.modelId;
            if (!modelIdToAllRequestedTasks.has(modelId)) {
                modelIdToAllRequestedTasks.set(modelId, []);
                modelIdToResolvedParams.set(
                    modelId,
                    resolveInputBenchmarkingModelParams(
                        inputParams,
                        inputBundle.llmServiceIdentifier
                    )
                );
            }
            const requestedTasks = modelIdToAllRequestedTasks.get(modelId)!;
            bundleTasks.forEach((task) => requestedTasks.push(task));
        }
    }
    const benchmarkingItems: BenchmarkingItem[] = [];
    for (const [
        modelId,
        requestedTasks,
    ] of modelIdToAllRequestedTasks.entries()) {
        const uniqueTasks = makeUnique(requestedTasks);
        uniqueTasks
            .map((task) => {
                return {
                    task: task,
                    params: modelIdToResolvedParams.get(modelId)!,
                };
            })
            .forEach((item) => benchmarkingItems.push(item));
    }
    return benchmarkingItems;
}

function makeUnique(
    requestedTasks: CompletionGenerationTask[]
): CompletionGenerationTask[] {
    // TODO: implement more efficient algorithm?
    const uniqueTasks = [];
    for (const requestedTask of requestedTasks) {
        let isUnique = true;
        for (const uniqueTask of uniqueTasks) {
            if (
                uniqueTask.sourceFilePath === requestedTask.sourceFilePath &&
                uniqueTask.targetType === requestedTask.targetType &&
                uniqueTask.targetPositionRange.equalsTo(
                    requestedTask.targetPositionRange
                )
            ) {
                isUnique = false;
                break;
            }
        }
        if (isUnique) {
            uniqueTasks.push(requestedTask);
        }
    }
    return uniqueTasks;
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
        llmServiceIdentifier: llmServiceIdentifier,
    };
}

// TODO: add bundle id to the request, so as to make possible to just filter by it here
function constructTasksForBundleTargets(
    bundleTargets: InputTargets,
    workspaceToParsedFileTargets: WorkspaceToParsedFileTargets
): CompletionGenerationTask[] {
    const tasks: CompletionGenerationTask[] = [];
    for (const [
        workspaceRoot,
        filePathToFileTargets,
    ] of bundleTargets.entries()) {
        const parsedFileTargets =
            workspaceToParsedFileTargets.get(workspaceRoot);
        if (parsedFileTargets === undefined) {
            throw Error(
                `no parsed file targets data found for requested workspace root: "${workspaceRoot?.directoryPath}"`
            );
        }
        for (const [filePath, fileTarget] of filePathToFileTargets.entries()) {
            const parsedFileTarget = parsedFileTargets.get(filePath);
            if (parsedFileTarget === undefined) {
                throw Error(
                    `no parsed file target data found for requested source file: "${filePath}"`
                );
            }

            // find all theorems targets for this bundle
            const targetTypesForAllTheorems = [];
            if (fileTarget.allTheoremsAsAdmitTargets) {
                targetTypesForAllTheorems.push(TargetType.ADMIT);
            }
            if (fileTarget.allTheoremsAsProveTheoremTargets) {
                targetTypesForAllTheorems.push(TargetType.PROVE_THEOREM);
            }
            targetTypesForAllTheorems.forEach((targetType) => {
                const bundleTaskTargets =
                    parsedFileTarget.extractedTaskTargets.filter(
                        (parsedTaskTarget) =>
                            parsedTaskTarget.targetType === targetType
                    );
                bundleTaskTargets.forEach((taskTarget) =>
                    tasks.push(
                        new CompletionGenerationTask(
                            taskTarget.targetGoalToProve,
                            taskTarget.targetPositionRange,
                            taskTarget.targetType,
                            parsedFileTarget.parsedFile,
                            taskTarget.sourceTheorem,
                            workspaceRoot
                        )
                    )
                );
            });

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
                targetTypes.forEach((targetType) => {
                    const bundleTaskTargets =
                        parsedFileTarget.extractedTaskTargets.filter(
                            (parsedTaskTarget) =>
                                parsedTaskTarget.sourceTheorem.name ===
                                    theoremName &&
                                parsedTaskTarget.targetType === targetType
                        );
                    bundleTaskTargets.forEach((taskTarget) =>
                        tasks.push(
                            new CompletionGenerationTask(
                                taskTarget.targetGoalToProve,
                                taskTarget.targetPositionRange,
                                taskTarget.targetType,
                                parsedFileTarget.parsedFile,
                                taskTarget.sourceTheorem,
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
