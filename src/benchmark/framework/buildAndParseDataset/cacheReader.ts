import { ValidateFunction } from "ajv";

import {
    AjvMode,
    buildAjv,
    failedAjvValidatorErrorsAsString,
} from "../../../utils/ajvErrorsHandling";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    exists,
    getDatasetDir,
    isFile,
    joinPaths,
    readFile,
    relativizeAbsolutePaths,
    resolveAsAbsolutePath,
} from "../utils/fsUtils";
import { packIntoMap } from "../utils/mapUtils";

import { DatasetCacheModels } from "./cacheModels";

export function readRequestedFilesCache(
    requestedFilePaths: string[],
    datasetCacheDirectoryPath: string,
    parentLogger: BenchmarkingLogger
): Map<string, DatasetCacheModels.CachedCoqFile> {
    const datasetDir = getDatasetDir();
    const cacheDir = resolveAsAbsolutePath(datasetCacheDirectoryPath);
    const cachedFileValidator = buildAjv(AjvMode.COLLECT_ALL_ERRORS).compile(
        DatasetCacheModels.cachedCoqFileSchema
    );
    const logger = parentLogger.createChildLoggerWithIdentifier(
        "[Dataset Cache Reader]"
    );
    return packIntoMap(
        requestedFilePaths,
        (filePath) => filePath,
        (resolvedSourceFilePath) => {
            const filePathRelativeToDataset = relativizeAbsolutePaths(
                datasetDir,
                resolvedSourceFilePath
            );
            const resolvedCachedFilePath = joinPaths(
                cacheDir,
                filePathRelativeToDataset
            );
            if (
                !(
                    exists(resolvedCachedFilePath) &&
                    isFile(resolvedCachedFilePath)
                )
            ) {
                return undefined;
            }
            return readCachedCoqFile(
                resolvedCachedFilePath,
                resolvedSourceFilePath,
                cachedFileValidator,
                logger
            );
        }
    );
}

function readCachedCoqFile(
    cachedFilePath: string,
    sourceFilePath: string,
    cachedFileValidator: ValidateFunction<DatasetCacheModels.CachedCoqFile>,
    logger: BenchmarkingLogger
): DatasetCacheModels.CachedCoqFile | undefined {
    const cachedFileContent = readFile(cachedFilePath, (error) => {
        logger.error(
            `Failed to read a cache file "${cachedFilePath}" for a source file "${sourceFilePath}": ${error.message}`
        );
        return undefined;
    });
    if (cachedFileContent === undefined) {
        return undefined;
    }
    try {
        const cachedCoqFile = JSON.parse(
            cachedFileContent
        ) as DatasetCacheModels.CachedCoqFile;
        if (!cachedFileValidator(cachedCoqFile)) {
            logger.error(
                `Failed to parse a cache file "${cachedFilePath}", bad format: ${failedAjvValidatorErrorsAsString(cachedFileValidator)}`
            );
            return undefined;
        }
        logger.debug(
            `Successfully found & read a cache file "${cachedFilePath}" for a source file "${sourceFilePath}"`
        );
        return cachedCoqFile;
    } catch (e) {
        logger.error(
            `Failed to parse a cache file "${cachedFilePath}", bad format: ${e as Error}`
        );
        return undefined;
    }
}
