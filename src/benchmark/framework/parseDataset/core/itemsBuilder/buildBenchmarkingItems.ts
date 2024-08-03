import { ModelParams } from "../../../../../llm/llmServices/modelParams";
import { resolveOrThrow } from "../../../../../llm/llmServices/utils/resolveOrThrow";

import { InputBenchmarkingModelParams } from "../../../experiment/inputBenchmarkingModelParams";
import { BenchmarkingItem } from "../../../structures/benchmarkingItem";
import { BenchmarkingModelParams } from "../../../structures/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../../structures/completionGenerationTask";
import { InputBenchmarkingBundle } from "../../../structures/inputBenchmarkingBundle";
import { LLMServiceIdentifier } from "../../../structures/llmServiceIdentifier";
import { EqualitySet } from "../../../utils/equalitySet";
import {
    LLMServicesParamsResolvers,
    createParamsResolvers,
    getParamsResolver,
} from "../../../utils/llmServicesUtils";
import { getOrPut } from "../../../utils/mapUtils";
import { resolveTheoremsRanker } from "../../../utils/resolveTheoremsRanker";
import { DatasetCacheHolder } from "../../cacheStructures/cacheHolders";

import { constructTasksForBundleTargets } from "./constructTasks";

export function buildBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder
): BenchmarkingItem[] {
    const [modelIdToRequestedTasks, modelIdToResolvedParams] =
        buildTasksAndResolveParams(inputBundles, datasetCache);

    return constructBenchmarkingItems(
        modelIdToRequestedTasks,
        modelIdToResolvedParams
    );
}

function buildTasksAndResolveParams(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder
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
    const paramsResolvers = createParamsResolvers();

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
                            bundle.llmServiceIdentifier,
                            paramsResolvers
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

function resolveInputBenchmarkingModelParams(
    inputParams: InputBenchmarkingModelParams.Params,
    llmServiceIdentifier: LLMServiceIdentifier,
    paramsResolvers: LLMServicesParamsResolvers
): BenchmarkingModelParams<ModelParams> {
    const paramsResolver = getParamsResolver(
        llmServiceIdentifier,
        paramsResolvers
    );
    const { ranker, ...pureInputModelParams } = inputParams;
    return {
        theoremRanker: resolveTheoremsRanker(inputParams.ranker),
        modelParams: resolveOrThrow(paramsResolver, pureInputModelParams),
        llmServiceIdentifier: llmServiceIdentifier,
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