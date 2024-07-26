import {
    stringifyAnyValue,
    stringifyDefinedValue,
} from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { TargetType } from "../../structures/completionGenerationTask";
import { serializeTheoremData } from "../../structures/theoremData";
import { serializeCodeElementRange } from "../../structures/utilStructures";
import {
    getDatasetDir,
    joinPaths,
    relativizeAbsolutePaths,
    writeToFile,
} from "../../utils/fsUtils";
import { serializeGoal } from "../../utils/goalParser";
import { packIntoMappedObject } from "../../utils/mapUtils";
import { extractTheoremFisrtProofStep } from "../../utils/proofTargetExtractor";
import {
    CacheHolderData,
    DatasetCacheHolder,
} from "../cacheStructures/cacheHolders";
import { DatasetCacheModels } from "../cacheStructures/cacheModels";

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
        const workspacePathRelativeToDataset = relativizeAbsolutePaths(
            getDatasetDir(),
            workspacePath
        );
        const successfullyCachedFiles = [];

        for (const [filePath, cachedFile] of workspaceCache.entries()) {
            const serializedCachedFile =
                SerializeCacheHolders.serializeCachedCoqFileData(cachedFile);
            const cachedFilePath = joinPaths(
                datasetCacheDirectoryPath,
                workspacePathRelativeToDataset,
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

namespace SerializeCacheHolders {
    export function serializeCachedCoqFileData(
        cachedCoqFileData: CacheHolderData.CachedCoqFileData
    ): DatasetCacheModels.CachedCoqFile {
        return {
            allFileTheorems: packIntoMappedObject(
                cachedCoqFileData.getAllCachedTheorems(),
                (cachedTheoremData: CacheHolderData.CachedTheoremData) =>
                    cachedTheoremData.theoremData.name,
                (cachedTheoremData: CacheHolderData.CachedTheoremData) =>
                    serializeCachedTheoremData(
                        cachedTheoremData,
                        joinPaths(
                            cachedCoqFileData.workspacePath,
                            cachedCoqFileData.filePathRelativeToWorkspace
                        )
                    )
            ),
            fileLines: cachedCoqFileData.getFileLines(),
            fileVersion: cachedCoqFileData.getFileVersion(),
            filePathRelativeToWorkspace:
                cachedCoqFileData.filePathRelativeToWorkspace,
        };
    }

    export function serializeCachedTheoremData(
        cachedTheoremData: CacheHolderData.CachedTheoremData,
        sourceFilePath: string
    ): DatasetCacheModels.CachedTheorem {
        const proofTargets = cachedTheoremData.getCachedTargetsByType(
            TargetType.PROVE_THEOREM
        );
        if (proofTargets.length > 1) {
            const errorMessageLines = [
                "Cache serialization invariant failed: ",
                "there are more than 1 proof targets stored for the theorem.",
                `\n\tCause: proof targets ${stringifyAnyValue(proofTargets)} of theorem "${cachedTheoremData.theoremData.name}" from ${sourceFilePath} file`,
            ];
            throw Error(errorMessageLines.join(""));
        }
        return {
            theorem: serializeTheoremData(cachedTheoremData.theoremData),
            proofTarget:
                proofTargets.length === 1
                    ? serializeCachedTargetData(proofTargets[0])
                    : ({
                          goalToProve: undefined,
                          positionRange: serializeCodeElementRange(
                              extractTheoremFisrtProofStep(
                                  cachedTheoremData.theoremData
                              ).range
                          ),
                      } as DatasetCacheModels.CachedTarget),
            admitTargets: cachedTheoremData
                .getCachedTargetsByType(TargetType.ADMIT)
                .map((cachedTargetData) =>
                    serializeCachedTargetData(cachedTargetData)
                ),
        };
    }

    export function serializeCachedTargetData(
        cachedTargetData: CacheHolderData.CachedTargetData
    ): DatasetCacheModels.CachedTarget {
        const goalToProve = cachedTargetData.getGoalToProve();
        return {
            goalToProve:
                goalToProve === undefined
                    ? undefined
                    : serializeGoal(goalToProve),
            positionRange: serializeCodeElementRange(
                cachedTargetData.positionRange
            ),
        };
    }
}
