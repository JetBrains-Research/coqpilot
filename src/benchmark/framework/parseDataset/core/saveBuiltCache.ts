import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../../structures/inputParameters/datasetCaching";
import { ExperimentRunOptions } from "../../structures/inputParameters/experimentRunOptions";
import { rewriteDatasetCache } from "../cacheHandlers/cacheWriter";
import { DatasetCacheHolder } from "../cacheStructures/cacheHolders";

export function saveBuiltCache(
    datasetCache: DatasetCacheHolder,
    runOptions: ExperimentRunOptions,
    logger: BenchmarkingLogger
) {
    const prepareToSaveCacheRecord = logger
        .asOneRecord()
        .info(`Selected cache usage mode: ${runOptions.datasetCacheUsage}`);

    const cacheMode = runOptions.datasetCacheUsage;
    if (shouldWriteBuiltCache(cacheMode)) {
        prepareToSaveCacheRecord.info(
            `Built data will be saved into ${runOptions.datasetCacheDirectoryPath}`
        );
        /**
         * Explanation note for the `EXTEND_CACHE_WITH_MISSING_TARGETS` mode: why does it actually work.
         * In the current implementation, the `datasetCache` contains **not** all the cache content,
         * but only the cache for the requested files plus the parsed data for the missing targets.
         * Thus, workspace cache directories should not be blindly cleared:
         * larger cache (than for the requested targets) might be lost.
         * However, it is save to rewrite **all** the files present in the `datasetCache`:
         * due to the invariant, file cache is always read and maintained in-memory completely
         * (i.e. with all its internal targets and metadata).
         * Therefore, saving all the `datasetCache` files always extends the cache and never loses it.
         */
        rewriteDatasetCache(
            datasetCache,
            runOptions.datasetCacheDirectoryPath,
            shouldClearWorkspaceCacheDirectories(cacheMode),
            logger
        );
    } else {
        prepareToSaveCacheRecord.info("Built data will not be saved");
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

function shouldClearWorkspaceCacheDirectories(
    cacheMode: DatasetCacheUsageMode
): boolean {
    switch (cacheMode) {
        case DatasetCacheUsageMode.NO_CACHE_USAGE:
        case DatasetCacheUsageMode.READ_CACHE_ONLY:
            throw Error(
                `${cacheMode} mode should cause no modification of cache files; thus, this function should not have been called`
            );
        case DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS:
            return false;
        case DatasetCacheUsageMode.REBUILD_CACHE_FOR_REQUESTED_TARGETS:
            return true;
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_FILES:
            return true;
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS:
            return true;
    }
}
