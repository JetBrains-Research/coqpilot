import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../../structures/benchmarkingItem";
import { ExperimentRunOptions } from "../../structures/experimentRunOptions";
import { InputBenchmarkingBundle } from "../../structures/inputBenchmarkingBundle";
import { DatasetInputTargets } from "../../structures/inputTargets";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { DatasetCacheHolder } from "../cacheStructures/cacheHolders";
import { logBenchmarkingItems } from "../utils/logBenchmarkingItems";

import { filterRequestedTargetsMissingInCache } from "./filterTargetsMissingInCache";
import { buildBenchmarkingItems } from "./itemsBuilder/buildBenchmarkingItems";
import { parseMissingTargetsAndUpdateCache } from "./parseMissingTargets";
import { saveBuiltCache } from "./saveBuiltCache";

/**
 * This is the core dataset parsing function that creates `BenchmarkingItem`-s.
 * In general, it reads the dataset cache and parses the dataset source projects to build the items,
 * optionally updating the cache for the next runs.
 *
 * Pipeline steps in more details. This function:
 * 1. *(optional)* Reads cache of the previously parsed dataset.
 * 2. Determines, which of the requested targets are not present in the cache.
 * 3. If there are some, parses them (the missing targets) from the source Coq projects via subprocesses.
 * 4. From the data obtained from the cache and dataset parsing, it constructs `BenchmarkingItem`-s.
 * 5. *(optional)* Finally, the updated cache is saved to the cache directory.
 *
 * *Implementation note:* for the sake of simplicity and clarity, the whole pipeline *always*
 * uses cache holders structures. Namely:
 * * First, whether the cache should be read or not, the cache holder structures are initialized (maybe as empty ones).
 * * After the missing requested targets are parsed via the subprocesses,
 *   the results are merged into the cache holder structures.
 * * Later, these cache holders are used to build benchmarking items: essentially,
 *   the cache holders simply provide access to the whole dataset data present (both cached and parsed).
 * * Finally, the cache holders might be saved in the cache directory
 *   (updating the old cache), if it is requested.
 */
export async function parseDatasetForBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle[],
    mergedRequestedTargets: DatasetInputTargets,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: AsyncScheduler,
    logger: BenchmarkingLogger
): Promise<BenchmarkingItem[]> {
    if (mergedRequestedTargets.isEmpty()) {
        logger.info(
            "No benchmarking targets selected. Configure some and try again."
        );
        return [];
    }

    const datasetCache = new DatasetCacheHolder();
    for (const [
        workspaceRoot,
        workspaceTargets,
    ] of mergedRequestedTargets.entries()) {
        const [missingTargets, workspaceCache] =
            filterRequestedTargetsMissingInCache(
                workspaceTargets,
                workspaceRoot,
                runOptions,
                logger
            );

        if (missingTargets.isEmpty()) {
            logger.debug(
                "No missing targets to parse from sources: all data can be retrieved from cache"
            );
        } else {
            logger.debug(
                `Missing targets to parse from sources:\n${missingTargets.toString("  ")}`
            );
            await parseMissingTargetsAndUpdateCache(
                missingTargets,
                workspaceCache,
                workspaceRoot,
                runOptions,
                subprocessesScheduler,
                logger
            );
        }

        datasetCache.addWorkspaceCache(
            workspaceRoot.directoryPath,
            workspaceCache
        );
    }

    const benchmarkingItems = buildBenchmarkingItems(
        inputBundles,
        datasetCache
    );
    logger
        .asOneRecord()
        .info(
            `Successfully constructed ${benchmarkingItems.length} benchmarking item(s)`,
            undefined,
            ""
        )
        .debug(`:\n${logBenchmarkingItems(benchmarkingItems)}`);

    saveBuiltCache(datasetCache, runOptions, logger);

    return benchmarkingItems;
}
