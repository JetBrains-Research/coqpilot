import { modelName } from "../../../llm/llmServices/utils/modelParamsAccessors";

import { stringifyAnyValue } from "../../../utils/printers";
import { millisToString } from "../../../utils/time";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingOptions } from "../structures/benchmarkingCore/benchmarkingOptions";
import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";
import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";
import { LLMServiceIdentifier } from "../structures/common/llmServiceIdentifier";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { abortAsFailFast } from "../utils/asyncUtils/abortUtils";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import { groupBy, mapValues } from "../utils/collectionUtils/mapUtils";
import { getShortName } from "../utils/commonStructuresUtils/llmServicesUtils";
import { translateToSafeFileName } from "../utils/fileUtils/fileNameUtils";
import {
    createDirectory,
    getDatasetDir,
    joinPaths,
    provideEmptyDirectoryOrThrow,
    relativizeAbsolutePaths,
    writeToFile,
} from "../utils/fileUtils/fs";
import { prependWithZeros } from "../utils/serializationUtils";
import { benchmarkingInvariantFailed } from "../utils/throwErrors";

import { executeBenchmarkingTask } from "./executeBenchmarkingTask";
import { TimeMark } from "./singleCompletionGeneration/measureTimeUtils";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

namespace ArtifactsNames {
    export const itemsReportsDir = "items";
    export const experimentReportFileName = "experiment-report.json";
}

export async function benchmark(
    benchmarkingItems: BenchmarkingItem[],
    resolvedArtifactsDirPath: string,
    experimentRunOptions: ExperimentRunOptions,
    parentLogger: BenchmarkingLogger,
    totalTime: TimeMark,
    proofsChecker: AbstractProofsChecker
): Promise<ExperimentResults> {
    provideEmptyDirectoryOrThrow(resolvedArtifactsDirPath, "artifacts");
    const itemsDirPath = createDirectory(
        true,
        resolvedArtifactsDirPath,
        ArtifactsNames.itemsReportsDir
    );

    const modelsSchedulers = ModelsSchedulers.buildModelsSchedulers(
        benchmarkingItems,
        experimentRunOptions
    );
    const options = extractBenchmarkingOptions(experimentRunOptions);
    const abortController = new AbortController();
    const abortSignal = abortController.signal;

    const itemsPromises: Promise<BenchmarkedItem | undefined>[] = [];
    for (let i = 0; i < benchmarkingItems.length; i++) {
        const item = benchmarkingItems[i];
        const itemArtifactsDirPath = createDirectory(
            true,
            itemsDirPath,
            buildUniqueItemReportDirName(i, benchmarkingItems.length - 1, item)
        );

        const itemLogger = buildItemLogger(item, parentLogger);
        const modelsScheduler = ModelsSchedulers.getScheduler(
            modelsSchedulers,
            item,
            itemLogger
        );
        itemsPromises.push(
            executeBenchmarkingTask(
                item,
                itemArtifactsDirPath,
                options,
                itemLogger,
                modelsScheduler,
                proofsChecker,
                abortSignal
            )
        );
    }

    const benchmarkedItems = await runBenchmarkingItems(
        itemsPromises,
        options,
        abortController
    );
    parentLogger
        .asOneRecord()
        .info("Finish experiment benchmarking: ", "blue")
        .info(
            `${benchmarkedItems.length} completed / ${benchmarkingItems.length} total items`
        )
        .debug(
            `Total elapsed time: ${millisToString(totalTime.measureElapsedMillis())}`
        );

    const experimentResult = new ExperimentResults(benchmarkedItems);

    const experimentReportPath = joinPaths(
        resolvedArtifactsDirPath,
        ArtifactsNames.experimentReportFileName
    );
    writeToFile(experimentResult.asJson(), experimentReportPath, (e) =>
        parentLogger
            .asOneRecord()
            .error(
                `Failed to save experiment results into ${experimentReportPath}`
            )
            .debug(`Cause: ${stringifyAnyValue(e)}`)
    );

    return experimentResult;
}

/**
 * @returns `BenchmarkedItem`-s of the completed benchmarking items (failed once, returning `undefined`, are not included).
 */
async function runBenchmarkingItems(
    itemsPromises: Promise<BenchmarkedItem | undefined>[],
    options: BenchmarkingOptions,
    abortController: AbortController
): Promise<BenchmarkedItem[]> {
    if (options.failFast) {
        try {
            const results = await Promise.all(itemsPromises);
            return results.filter(
                (result) => result !== undefined
            ) as BenchmarkedItem[];
        } catch (e) {
            abortAsFailFast(abortController);
            throw e;
        }
    } else {
        /*
         * Even though `itemsPromises` should not be rejected if the `options.failFast === false`
         * (`executeBenchmarkingTask` catches all errors and returns `undefined` in such failure cases),
         * using `Promise.allSettled` guarantees the expected behaviour of waiting for all promises to resolve
         * that could become necessary in the future if `executeBenchmarkingTask` behaviour changes.
         */
        const settledResults = await Promise.allSettled(itemsPromises);
        return settledResults
            .filter(
                (result) =>
                    result.status === "fulfilled" && result.value !== undefined
            )
            .map(
                (result) =>
                    (result as PromiseFulfilledResult<BenchmarkedItem>).value
            );
    }
}

namespace ModelsSchedulers {
    export type Mapping = Map<LLMServiceIdentifier, ModelNameToModelsScheduler>;
    export type ModelNameToModelsScheduler = Map<string, AsyncScheduler>;

    const NO_MODEL_NAME_KEYWORD = "";

    export function getModelNameOrNoModelNameKeyword(
        item: BenchmarkingItem
    ): string {
        return modelName(item.params.modelParams) ?? NO_MODEL_NAME_KEYWORD;
    }

    export function getScheduler(
        modelsSchedulers: Mapping,
        item: BenchmarkingItem,
        itemLogger: BenchmarkingLogger
    ): AsyncScheduler {
        return (
            modelsSchedulers
                .get(item.params.llmServiceIdentifier)
                ?.get(
                    ModelsSchedulers.getModelNameOrNoModelNameKeyword(item)
                ) ??
            benchmarkingInvariantFailed(
                itemLogger,
                "no models scheduler for the benchmarking item"
            )
        );
    }

    export function buildModelsSchedulers(
        benchmarkingItems: BenchmarkingItem[],
        experimentRunOptions: ExperimentRunOptions
    ): Mapping {
        return mapValues(
            groupBy(
                benchmarkingItems,
                (item) => item.params.llmServiceIdentifier
            ),
            (
                _: LLMServiceIdentifier,
                sameLLMServiceItems: BenchmarkingItem[]
            ) => {
                const sameLLMServiceItemsByModelNames = groupBy(
                    sameLLMServiceItems,
                    (item) => getModelNameOrNoModelNameKeyword(item)
                );
                return mapValues(
                    sameLLMServiceItemsByModelNames,
                    (modelName: string, sameModelItems: BenchmarkingItem[]) =>
                        new AsyncScheduler(
                            experimentRunOptions.maxParallelGenerationRequestsToModel,
                            experimentRunOptions.enableModelsSchedulingDebugLogs,
                            `Models Scheduler for: ${getShortName(sameModelItems[0].params.llmServiceIdentifier)}${modelName === "" ? "" : `, "${modelName}"`}`
                        )
                );
            }
        );
    }
}

function extractBenchmarkingOptions(
    experimentRunOptions: ExperimentRunOptions
): BenchmarkingOptions {
    const {
        failFast,
        logFailFastTasksAborting,
        proofGenerationRetries,
        logTeamCityStatistics,
    } = experimentRunOptions;
    return {
        failFast: failFast,
        logFailFastTasksAborting: logFailFastTasksAborting,
        proofGenerationRetries: proofGenerationRetries,
        logTeamCityStatistics: logTeamCityStatistics,
    };
}

function buildUniqueItemReportDirName(
    itemIndex: number,
    maxIndex: number,
    item: BenchmarkingItem
): string {
    const augmentedIndex = prependWithZeros(itemIndex, maxIndex);
    const modelId = item.params.modelParams.modelId;
    const fileIdentifier = relativizeAbsolutePaths(
        getDatasetDir(),
        item.task.sourceFilePath
    );
    const unsafeFileName = [
        `${augmentedIndex}-${getShortName(item.params.llmServiceIdentifier)}-${modelId}`,
        `-${fileIdentifier}-${item.task.sourceTheorem.name}`,
    ].join("");
    return translateToSafeFileName(unsafeFileName);
}

function buildItemLogger(
    item: BenchmarkingItem,
    parentLogger: BenchmarkingLogger
): BenchmarkingLogger {
    const task = item.task;
    const params = item.params;
    return parentLogger.createChildLoggerWithIdentifier(
        [
            "[",
            `modelId: "${params.modelParams.modelId}", `,
            `theorem: \`${task.sourceTheorem.name}\`, `,
            `completion position: ${task.targetPositionRange.start}`,
            "]\n",
            `[file: ${task.sourceFilePath}]`,
        ].join("")
    );
}
