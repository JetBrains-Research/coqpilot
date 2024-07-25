import { stringifyDefinedValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { joinPaths, writeToFile } from "../utils/fsUtils";

import { DatasetCacheHolder } from "./cacheHolder";

/**
 * Since saving the cache does not affect the correctness of the system,
 * this function does not throw errors, but only reports them via the logger.
 *
 * @returns true if cache was successfully saved, false otherwise.
 */
export function rewriteDatasetCache(
    updatedDatasetCache: DatasetCacheHolder,
    datasetCacheDirectoryPath: string,
    parentLogger: BenchmarkingLogger
): boolean {
    // TODO: support cache directory cleaning here
    const logger = parentLogger.createChildLoggerWithIdentifier(
        `[Dataset Cache Writer, cache path = ${datasetCacheDirectoryPath}]`
    );

    for (const [
        workspacePath,
        workspaceCache,
    ] of updatedDatasetCache.entries()) {
        const successfullyCachedFiles = [];
        for (const [filePath, cachedFile] of workspaceCache.entries()) {
            const serializedCachedFile = cachedFile.serializeToCacheModel();
            const cachedFilePath = joinPaths(
                datasetCacheDirectoryPath,
                serializedCachedFile.filePathRelativeToWorkspace
            );
            const fileSuccessfullySaved = writeToFile(
                stringifyDefinedValue(serializedCachedFile, 2),
                cachedFilePath,
                (error) => {
                    logger
                        .asOneRecord()
                        .error(
                            `Failed to save cached file ${cachedFilePath}: ${error.message}.`
                        )
                        .error(
                            `(!) Now cache is invalidated. Clear ${datasetCacheDirectoryPath} cache directory and try again.`
                        );
                    return false;
                }
            );
            if (fileSuccessfullySaved) {
                successfullyCachedFiles.push(filePath);
            } else {
                return false;
            }
        }
        logger
            .asOneRecord()
            .debug(`Successfuly saved workspace cache for ${workspacePath}:`)
            .debug(
                `${successfullyCachedFiles.map((filePath) => `* ${filePath}`).join("\n")}`
            );
    }

    logger.info(`Successfully saved cache into ${datasetCacheDirectoryPath}.`);
    return true;
}
