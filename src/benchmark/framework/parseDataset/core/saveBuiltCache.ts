import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../../structures/datasetCaching";
import { ExperimentRunOptions } from "../../structures/experimentRunOptions";
import { rewriteDatasetCache } from "../cacheHandlers/cacheWriter";
import { DatasetCacheHolder } from "../cacheStructures/cacheHolders";

export function saveBuiltCache(
    datasetCache: DatasetCacheHolder,
    runOptions: ExperimentRunOptions,
    logger: BenchmarkingLogger
) {
    const prepareToSaveCacheRecord = logger
        .asOneRecord()
        .info(`Selected cache usage mode: ${runOptions.datasetCacheUsage}.`);

    if (shouldWriteBuiltCache(runOptions.datasetCacheUsage)) {
        prepareToSaveCacheRecord.info(
            `Built data will be saved into ${runOptions.datasetCacheDirectoryPath}.`
        );
        rewriteDatasetCache(
            datasetCache,
            runOptions.datasetCacheDirectoryPath,
            true,
            logger
        );
    } else {
        prepareToSaveCacheRecord.info("Built data will not be saved.");
    }
}

function shouldWriteBuiltCache(cacheMode: DatasetCacheUsageMode): boolean {
    switch (cacheMode) {
        case DatasetCacheUsageMode.NO_CACHE_USAGE:
            return false;
        case DatasetCacheUsageMode.READ_CACHE_ONLY:
            return false;
        case DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS:
            return true;
        case DatasetCacheUsageMode.REBUILD_CACHE_FOR_REQUESTED_TARGETS:
            return true;
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_FILES:
            return true;
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS:
            return true;
    }
}
