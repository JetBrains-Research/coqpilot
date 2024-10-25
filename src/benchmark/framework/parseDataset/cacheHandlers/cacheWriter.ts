import { stringifyAnyValue, toJsonString } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { TargetType } from "../../structures/benchmarkingCore/completionGenerationTask";
import { serializeCodeElementRange } from "../../structures/common/codeElementPositions";
import { serializeTheoremData } from "../../structures/parsedCoqFile/theoremData";
import { packIntoMappedObject } from "../../utils/collectionUtils/mapUtils";
import { serializeGoal } from "../../utils/coqUtils/goalParser";
import { extractTheoremFisrtProofStep } from "../../utils/coqUtils/proofTargetExtractor";
import {
    clearDirectory,
    getDatasetDir,
    joinPaths,
    relativizeAbsolutePaths,
    writeToFile,
} from "../../utils/fileUtils/fs";
import {
    CacheHolderData,
    DatasetCacheHolder,
} from "../cacheStructures/cacheHolders";
import { DatasetCacheModels } from "../cacheStructures/cacheModels";
import { joinJsonExtension } from "../utils/fileJsonExtension";

/**
 * Since saving the cache does not affect the correctness of the system,
 * this function does not throw errors, but only reports them via the logger.
 *
 * @returns true if cache was successfully saved, false otherwise.
 */
export function rewriteDatasetCache(
    updatedDatasetCache: DatasetCacheHolder,
    datasetCacheDirectoryPath: string,
    clearWorkspaceCacheDirectories: boolean,
    parentLogger: BenchmarkingLogger
): boolean {
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
        const workspaceCacheDirectoryPath = joinPaths(
            datasetCacheDirectoryPath,
            workspacePathRelativeToDataset
        );
        if (clearWorkspaceCacheDirectories) {
            logger.debug(
                `Workspace cache directory will be cleared: ${workspaceCacheDirectoryPath}`
            );
            clearDirectory(workspaceCacheDirectoryPath);
        }

        const successfullyCachedFiles = [];
        for (const [filePath, cachedFile] of workspaceCache.entries()) {
            const serializedCachedFile =
                SerializeCacheHolders.serializeCachedCoqFileData(cachedFile);
            const cachedFilePath = joinPaths(
                workspaceCacheDirectoryPath,
                joinJsonExtension(
                    serializedCachedFile.filePathRelativeToWorkspace
                )
            );
            const fileSuccessfullySaved =
                writeToFile(
                    toJsonString(serializedCachedFile, 2),
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
                    },
                    true
                ) ?? true;
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

    logger.info(`Successfully saved cache into ${datasetCacheDirectoryPath}`);
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
            documentVersion: cachedCoqFileData.getDocumentVersion(),
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
