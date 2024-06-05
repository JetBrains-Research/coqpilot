import { stringifyAnyValue } from "../../../utils/printers";

import { executeBenchmarkingTask } from "./benchmarkCompletionGeneration/executeBenchmarkingTask";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
} from "./logging/benchmarkingLogger";
import { BenchmarkedItem } from "./structures/benchmarkedItem";
import { BenchmarkingItem } from "./structures/benchmarkingItem";
import { ExperimentResults } from "./structures/experimentResults";
import { ExperimentRunOptions } from "./structures/experimentRunOptions";
import {
    checkDirectoryIsEmpty,
    createDirectory,
    getLastName,
    joinPaths,
    writeToFile,
} from "./utils/fsUtils";
import { getShortName } from "./utils/llmServicesUtils";
import { SubprocessesScheduler } from "./utils/subprocessUtils/subprocessesScheduler";

namespace ArtifactsDirNames {
    export const itemsReportsDir = "items";
    export const experimentReportFileName = "experiment-report.json";
}

/**
 * TODO: add mutexes
 * - 1 per each group (by condition, same service & same model name)
 */
export async function benchmark(
    benchmarkingItems: BenchmarkingItem[],
    resolvedArtifactsDirPath: string,
    experimentRunOptions: ExperimentRunOptions
): Promise<ExperimentResults> {
    if (!checkDirectoryIsEmpty(resolvedArtifactsDirPath)) {
        throw Error(
            `artifacts directory should be empty: "${resolvedArtifactsDirPath}"`
        );
    }
    const itemsReportsDirPath = createDirectory(
        true,
        resolvedArtifactsDirPath,
        ArtifactsDirNames.itemsReportsDir
    );
    const parentLogger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
        experimentRunOptions.loggerSeverity
    );
    const subprocessesScheduler = new SubprocessesScheduler(
        experimentRunOptions.maxActiveSubprocessesNumber,
        experimentRunOptions.enableSchedulingDebugLogs
    );

    const itemsPromises: Promise<BenchmarkedItem | undefined>[] = [];
    for (let i = 0; i < benchmarkingItems.length; i++) {
        const item = benchmarkingItems[i];
        const itemReportPath = joinPaths(
            itemsReportsDirPath,
            buildUniqueItemReportFileName(i, benchmarkingItems.length - 1, item)
        );
        const itemLogger = buildItemLogger(item, parentLogger);
        itemsPromises.push(
            executeBenchmarkingTask(
                item,
                itemReportPath,
                itemLogger,
                subprocessesScheduler,
                experimentRunOptions
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

function buildUniqueItemReportFileName(
    itemIndex: number,
    maxIndex: number,
    item: BenchmarkingItem
): string {
    const augmentedIndex = prependWithZeros(itemIndex, maxIndex);
    const modelId = item.params.modelParams.modelId;
    const fileIdentifierPath =
        item.task.workspaceRoot !== undefined
            ? item.task.workspaceRoot.directoryPath
            : item.task.sourceFilePath;
    return translateToSafeFileName(
        [
            `${augmentedIndex}-${getShortName(item.llmServiceIdentifier)}-${modelId}`,
            `-${getLastName(fileIdentifierPath)}-${item.task.sourceTheorem.name}`,
            ".json",
        ].join("")
    );
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
            `modelId: ${params.modelParams.modelId}`,
            `theorem: ${task.sourceTheorem.name}`,
            `completion position: ${task.targetPositionRange.start}`,
            "]\n",
            `[file: ${task.sourceFilePath}]`,
        ].join("")
    );
}
