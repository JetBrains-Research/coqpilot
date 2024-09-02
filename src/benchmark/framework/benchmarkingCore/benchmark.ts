import { modelName } from "../../../llm/llmServices/utils/modelParamsAccessors";
import { millisToString } from "../../../llm/llmServices/utils/time";

import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";
import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";
import { LLMServiceIdentifier } from "../structures/common/llmServiceIdentifier";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { AsyncScheduler } from "../utils/asyncUtils/asyncScheduler";
import { groupBy, mapValues } from "../utils/collectionUtils/mapUtils";
import { getShortName } from "../utils/commonStructuresUtils/llmServicesUtils";
import {
    checkDirectoryIsEmpty,
    createDirectory,
    exists,
    getDatasetDir,
    joinPaths,
    relativizeAbsolutePaths,
    writeToFile,
} from "../utils/fsUtils";

import { executeBenchmarkingTask } from "./executeBenchmarkingTask";
import { TimeMark } from "./singleCompletionGeneration/measureUtils";
import { AbstractProofsChecker } from "./singleCompletionGeneration/proofsCheckers/abstractProofsChecker";

namespace ArtifactsDirNames {
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
    if (exists(resolvedArtifactsDirPath)) {
        if (!checkDirectoryIsEmpty(resolvedArtifactsDirPath)) {
            throw Error(
                `artifacts directory should be empty: "${resolvedArtifactsDirPath}"`
            );
        }
    } else {
        createDirectory(true, resolvedArtifactsDirPath);
    }
    const itemsReportsDirPath = createDirectory(
        true,
        resolvedArtifactsDirPath,
        ArtifactsDirNames.itemsReportsDir
    );

    const modelsSchedulers = ModelsSchedulers.buildModelsSchedulers(
        benchmarkingItems,
        experimentRunOptions
    );

    const itemsPromises: Promise<BenchmarkedItem | undefined>[] = [];
    for (let i = 0; i < benchmarkingItems.length; i++) {
        const item = benchmarkingItems[i];
        const itemReportPath = joinPaths(
            itemsReportsDirPath,
            buildUniqueItemReportFileName(i, benchmarkingItems.length - 1, item)
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
                itemReportPath,
                itemLogger,
                modelsScheduler,
                proofsChecker
            )
        );
    }

    const benchmarkingResults = await Promise.allSettled(itemsPromises);
    const benchmarkedItems = benchmarkingResults
        .filter(
            (result) =>
                result.status === "fulfilled" && result.value !== undefined
        )
        .map(
            (result) =>
                (result as PromiseFulfilledResult<BenchmarkedItem>).value
        );
    parentLogger
        .asOneRecord()
        .info("Finish experiment benchmarking: ", "magenta")
        .info(
            `${benchmarkedItems.length} completed / ${benchmarkingItems.length} total items`
        )
        .debug(
            `Total elapsed time: ${millisToString(totalTime.measureElapsedMillis())}`
        );

    const experimentResult = new ExperimentResults(benchmarkedItems);

    const experimentReportPath = joinPaths(
        resolvedArtifactsDirPath,
        ArtifactsDirNames.experimentReportFileName
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
        const modelsScheduler = modelsSchedulers
            .get(item.params.llmServiceIdentifier)
            ?.get(ModelsSchedulers.getModelNameOrNoModelNameKeyword(item));
        if (modelsScheduler === undefined) {
            itemLogger.error(
                "Unexpected error: no models scheduler for this benchmarking item"
            );
            throw Error(
                `Benchmarking failed: no models scheduler for the benchmarking item`
            );
        }
        return modelsScheduler;
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

function buildUniqueItemReportFileName(
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
    const safeFileName = translateToSafeFileName(
        [
            `${augmentedIndex}-${getShortName(item.params.llmServiceIdentifier)}-${modelId}`,
            `-${fileIdentifier}-${item.task.sourceTheorem.name}`,
        ].join("")
    );
    return `${safeFileName}.json`;
}

function prependWithZeros(n: number, maxN: number): string {
    const maxDigitsNumber = maxN.toString().length;
    const zerosToPrependNumber = maxDigitsNumber - n.toString().length;
    return `${"0".repeat(zerosToPrependNumber)}${n}`;
}

function translateToSafeFileName(text: string): string {
    return text.replace(/[_ &\/\\#,+()$~%.'":*?<>{}]/g, "-").toLowerCase();
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
