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

import { BaseInputBenchmarkingBundle } from "./experiment";
import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";
import { MergedInputTargets } from "./mergedInputTargets";

/**
 * Builds and parses requested Coq projects via subprocesses, then constructs benchmarking items.
 */
export async function buildBenchmarkingItems(
    inputBundles: BaseInputBenchmarkingBundle[],
    mergedInputTargets: MergedInputTargets,
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

type WorkspaceToParsedFileTargets = Map<WorkspaceRoot, ParsedFileTargets>;

async function buildAndParseRequestedCoqProjects(
    inputTargets: MergedInputTargets,
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
    workspaceRoot: WorkspaceRoot,
    sourceFileTargetsToParse: BuildAndParseCoqProjectBySubprocessSignature.ArgsModels.FilePathToFileTarget,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: SubprocessesScheduler,
    logger: BenchmarkingLogger
): Promise<ParsedFileTargets> {
    const executionResult = await buildAndParseCoqProjectInSubprocess(
        workspaceRoot,
        sourceFileTargetsToParse,
        false, // TODO: support turning projects building on
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
                `: ${Object.keys(sourceFileTargetsToParse).join(", ")}`,
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
    inputBundles: BaseInputBenchmarkingBundle[],
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
            inputBundle.bundleId,
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

function constructTasksForBundleTargets(
    bundleId: number,
    workspaceToParsedFileTargets: WorkspaceToParsedFileTargets
): CompletionGenerationTask[] {
    const tasks: CompletionGenerationTask[] = [];
    for (const [
        workspaceRoot,
        parsedFileTargets,
    ] of workspaceToParsedFileTargets.entries()) {
        for (const parsedFileTarget of parsedFileTargets.values()) {
            const bundleTaskTargets =
                parsedFileTarget.extractedTaskTargets.filter((taskTarget) =>
                    taskTarget.bundleIds.has(bundleId)
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
        }
    }
    return tasks;
}
