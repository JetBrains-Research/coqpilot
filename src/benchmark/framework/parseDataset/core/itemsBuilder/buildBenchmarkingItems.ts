import { ConfigurationError } from "../../../../../llm/llmServiceErrors";
import { ModelParams } from "../../../../../llm/llmServices/modelParams";
import { buildParamsResolutionMessages } from "../../../../../llm/llmServices/utils/paramsResolvers/kit/paramsResolutionAnalysis";

import { EqualitySet } from "../../../../../utils/collectionUtils/equalitySet";
import { getOrPut } from "../../../../../utils/collectionUtils/mapUtils";
import { unreachable } from "../../../../../utils/errors/throwErrors";
import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../../structures/benchmarkingCore/completionGenerationTask";
import { InputBenchmarkingBundle } from "../../../structures/inputParameters/inputBenchmarkingBundle";
import { InputBenchmarkingModelParams } from "../../../structures/inputParameters/inputBenchmarkingModelParams";
import { LLMServiceProvider } from "../../../structures/llmServiceProvider/llmServiceProvider";
import { resolveTheoremsRanker } from "../../../utils/inputResolutionUtils/resolveTheoremsRanker";
import { DatasetCacheHolder } from "../../cacheStructures/cacheHolders";

import { constructTasksForBundleTargets } from "./constructTasks";

export function buildBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder,
    logger: BenchmarkingLogger
): BenchmarkingItem[] {
    const [modelIdToRequestedTasks, modelIdToResolvedParams] =
        buildTasksAndResolveParams(inputBundles, datasetCache, logger);

    return constructBenchmarkingItems(
        modelIdToRequestedTasks,
        modelIdToResolvedParams
    );
}

function buildTasksAndResolveParams(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder,
    logger: BenchmarkingLogger
): [
    Map<string, CompletionGenerationTask[]>,
    Map<string, BenchmarkingModelParams<ModelParams>>,
] {
    const modelIdToRequestedTasks: Map<string, CompletionGenerationTask[]> =
        new Map();
    const modelIdToResolvedParams: Map<
        string,
        BenchmarkingModelParams<ModelParams>
    > = new Map();

    for (const bundle of inputBundles) {
        const bundleTasks: CompletionGenerationTask[] =
            constructTasksForBundleTargets(
                bundle.requestedTargets,
                datasetCache
            );

        // Attach constructed `bundleTasks` to all models requested in the bundle.
        for (const inputParams of bundle.inputBenchmarkingModelsParams) {
            const modelId = inputParams.modelId;
            const requestedTasks = getOrPut(
                modelIdToRequestedTasks,
                modelId,
                () => {
                    // If this model is met for the first time: resolve its parameters.
                    modelIdToResolvedParams.set(
                        modelId,
                        resolveInputBenchmarkingModelParams(
                            inputParams,
                            bundle.llmServiceProvider,
                            logger
                        )
                    );
                    return [] as CompletionGenerationTask[];
                }
            );
            requestedTasks.push(...bundleTasks);
        }
    }
    return [modelIdToRequestedTasks, modelIdToResolvedParams];
}

export function resolveInputBenchmarkingModelParams(
    inputParams: InputBenchmarkingModelParams.Params,
    llmServiceProvider: LLMServiceProvider,
    logger: BenchmarkingLogger
): BenchmarkingModelParams<ModelParams> {
    const paramsResolver = llmServiceProvider.getParamsResolver();
    const { ranker, ...pureInputModelParams } = inputParams;

    const resolutionResult = paramsResolver.resolve(pureInputModelParams);
    const resolutionMessages = buildParamsResolutionMessages(
        resolutionResult,
        inputParams.modelId
    );
    if (resolutionMessages.invalidConfigurationMessage !== undefined) {
        logger.error(resolutionMessages.invalidConfigurationMessage);
        throw new ConfigurationError(
            `Failed to resolve model parameters. ${resolutionMessages.invalidConfigurationMessage}`
        );
    }
    if (resolutionMessages.warningMessage !== undefined) {
        logger.error(
            `[Warning!] ${resolutionMessages.warningMessage}`,
            "yellow"
        );
    }
    return {
        theoremRanker: resolveTheoremsRanker(inputParams.ranker),
        modelParams:
            resolutionResult.resolved ??
            unreachable(
                "`resolutionResult.resolved` should be defined, ",
                "since params resolution analysis `invalidConfigurationMessage` is undefined"
            ),
        llmServiceProvider: llmServiceProvider,
    };
}

function constructBenchmarkingItems(
    modelIdToRequestedTasks: Map<string, CompletionGenerationTask[]>,
    modelIdToResolvedParams: Map<string, BenchmarkingModelParams<ModelParams>>
): BenchmarkingItem[] {
    const benchmarkingItems: BenchmarkingItem[] = [];
    for (const [modelId, requestedTasks] of modelIdToRequestedTasks.entries()) {
        const uniqueTasks = new EqualitySet<CompletionGenerationTask>(
            requestedTasks
        ).elements();

        for (const task of uniqueTasks) {
            benchmarkingItems.push({
                task: task,
                params: modelIdToResolvedParams.get(modelId)!,
            });
        }
    }
    return benchmarkingItems;
}
