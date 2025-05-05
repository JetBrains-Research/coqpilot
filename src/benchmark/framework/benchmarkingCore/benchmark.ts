import { buildErrorCompleteLog } from "../../../utils/errors/errorsUtils";
import { IllegalStateError } from "../../../utils/errors/throwErrors";
import {
    createDirectory,
    provideEmptyDirectoryOrThrow,
} from "../../../utils/fs/directoryUtils";
import { translateToSafeFileName } from "../../../utils/fs/fileNameUtils";
import { writeToFile } from "../../../utils/fs/fileUtils";
import {
    joinPaths,
    relativizeAbsolutePaths,
} from "../../../utils/fs/pathUtils";
import { getDatasetDir } from "../../../utils/fs/rootResolvers";
import { stringifyAnyValue } from "../../../utils/printers";
import { millisToString } from "../../../utils/time";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingOptions } from "../structures/benchmarkingCore/benchmarkingOptions";
import { BenchmarkedItem } from "../structures/benchmarkingResults/benchmarkedItem";
import { ExperimentResults } from "../structures/benchmarkingResults/experimentResults";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { BasicLLMServiceProvider } from "../structures/llmServiceProvider/implementors/basicLLMServiceProvider";
import {
    abortAsCriticalError,
    abortAsFailFast,
} from "../utils/asyncUtils/abortUtils";
import { prependWithZeros } from "../utils/serializationUtils";
import {
    buildFailedBenchmarkingInvariant,
    throwBenchmarkingError,
} from "../utils/throwErrors";

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
    provideEmptyDirectoryOrThrow(
        resolvedArtifactsDirPath,
        "artifacts",
        throwBenchmarkingError
    );
    const itemsDirPath = createDirectory(
        true,
        resolvedArtifactsDirPath,
        ArtifactsNames.itemsReportsDir
    );

    createModelsSchedulers(experimentRunOptions);

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
        const modelsScheduler = item.params.llmServiceProvider.selectScheduler(
            item.params.modelParams
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
        parentLogger,
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
    logger: BenchmarkingLogger,
    abortController: AbortController
): Promise<BenchmarkedItem[]> {
    try {
        /**
         * If fail-fast mode is enabled, then `executeBenchmarkingTask` rethrows all the errors.
         * Namely, the following `Promise.all` will be rejected as soon as an arbitrary error occurs.
         *
         * If fail-fast mode is disabled, then `executeBenchmarkingTask` guarantees to throw
         * only `IllegalStateError`-s, that indicate internal invariant violations
         * potentially leading to unpredictable behavior.
         * In other words, in such case, `Promise.all` will be rejected only and as soon as
         * any `IllegalStateError` occurs.
         */
        const results = await Promise.all(itemsPromises);
        return results.filter(
            (result) => result !== undefined
        ) as BenchmarkedItem[];
    } catch (err) {
        const criticalError = options.failFast
            ? err
            : err instanceof IllegalStateError
              ? err
              : buildFailedBenchmarkingInvariant(
                    logger,
                    "despite fail-fast mode is disabled, `executeBenchmarkingTask` threw an error, ",
                    "which is not of `IllegalStateError` type:\n",
                    buildErrorCompleteLog(err)
                );
        if (options.failFast) {
            abortAsFailFast(abortController);
        } else {
            logger
                .asOneRecord()
                .error(
                    "Critical error occurred, the benchmarking pipeline will be aborted"
                )
                .error(buildErrorCompleteLog(err));
            abortAsCriticalError(abortController, criticalError);
        }
        /**
         * Regardless of the mode enabled, all the promises should be awaited to finish gracefully.
         * This shouldn't take much time due to the abort signal being raised.
         */
        await Promise.allSettled(itemsPromises);
        throw criticalError;
    }
}

function createModelsSchedulers(experimentRunOptions: ExperimentRunOptions) {
    BasicLLMServiceProvider.setSchedulersProvidersSettings({
        enableModelsSchedulingDebugLogs:
            experimentRunOptions.enableModelsSchedulingDebugLogs,
        maxParallelism: experimentRunOptions.servicesMaxParallelism,
    });
}

function extractBenchmarkingOptions(
    experimentRunOptions: ExperimentRunOptions
): BenchmarkingOptions {
    const {
        failFast,
        logAbortingTasks,
        proofGenerationRetries,
        coqLspProvider,
        openDocumentTimeoutMillis,
        proofCheckTimeoutMillis,
        logTeamCityStatistics,
    } = experimentRunOptions;
    return {
        failFast: failFast,
        logAbortingTasks: logAbortingTasks,
        proofGenerationRetries: proofGenerationRetries,
        coqLspProvider: coqLspProvider,
        openDocumentTimeoutMillis: openDocumentTimeoutMillis,
        proofCheckTimeoutMillis: proofCheckTimeoutMillis,
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
        `${augmentedIndex}-${item.params.llmServiceProvider.toLogString(false)}-${modelId}`,
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
