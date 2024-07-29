import {
    AsOneRecordLogsBuilder,
    BenchmarkingLogger,
} from "../../logging/benchmarkingLogger";
import { TheoremData } from "../../structures/theoremData";
import { joinPaths, relativizeAbsolutePaths } from "../../utils/fsUtils";
import { mapValues } from "../../utils/mapUtils";
import {
    CacheHolderData,
    WorkspaceCacheHolder,
} from "../cacheStructures/cacheHolders";
import {
    ParsedFileHolder,
    ParsedFileTarget,
} from "../coqProjectParser/parsedWorkspaceHolder";

export function updateWorkspaceCache(
    workspaceCache: WorkspaceCacheHolder,
    filePath: string,
    parsedFileHolder: ParsedFileHolder,
    logger: BenchmarkingLogger
) {
    const cachedUpdaterLogger = logger.asOneRecord();

    const cachedFile = workspaceCache.getCachedFile(filePath);
    if (cachedFile === undefined) {
        cachedUpdaterLogger.debug(
            `Update in-memory cache with ${filePath} parsed targets:`
        );
        workspaceCache.addCachedFile(
            filePath,
            UpdateCacheHolders.buildCachedCoqFileData(
                parsedFileHolder,
                workspaceCache.workspacePath,
                cachedUpdaterLogger
            )
        );
        cachedUpdaterLogger.debug("");
    } else {
        cachedUpdaterLogger.debug(`Update cache for ${filePath}:`);
        UpdateCacheHolders.updateCachedCoqFileData(
            cachedFile,
            parsedFileHolder,
            cachedUpdaterLogger
        );
    }
}

namespace UpdateCacheHolders {
    export function updateCachedCoqFileData(
        cachedFile: CacheHolderData.CachedCoqFileData,
        parsedFileHolder: ParsedFileHolder,
        cacheUpdaterLogger: AsOneRecordLogsBuilder
    ) {
        const parsedFile = parsedFileHolder.parsedFile();
        const cachedResolvedPath = joinPaths(
            cachedFile.workspacePath,
            cachedFile.filePathRelativeToWorkspace
        );
        if (cachedResolvedPath !== parsedFile.filePath) {
            cacheUpdaterLogger
                .error(
                    "\nCache invariant failed: parsed targets file path is different from already cached one"
                )
                .debug(
                    `\tCause: cached file path ${cachedResolvedPath} != parsed file path ${parsedFile.filePath}`
                );
            throw Error(
                `Cache invariant failed: most likely, it has become invalid (${cachedFile.workspacePath} project cache)`
            );
        }

        if (cachedFile.getFileVersion() !== parsedFile.fileVersion) {
            cacheUpdaterLogger.debug(
                `* file version update: ${cachedFile.getFileVersion()} -> ${parsedFile.fileVersion}`
            );
        }
        cachedFile.updateFileLines(parsedFile.fileLines);
        cachedFile.updateFileVersion(parsedFile.fileVersion);

        for (const fileTarget of parsedFileHolder.targets()) {
            let cachedTheorem = cachedFile.getCachedTheorem(
                fileTarget.sourceTheorem.name
            );
            if (cachedTheorem === undefined) {
                cachedTheorem = new CacheHolderData.CachedTheoremData(
                    fileTarget.sourceTheorem
                );
                cacheUpdaterLogger.debug(`* cached new`, undefined, "");
            } else {
                cacheUpdaterLogger.debug(`* updated`, undefined, "");
            }
            cacheUpdaterLogger.debug(
                ` theorem: "${fileTarget.sourceTheorem.name}"`
            );

            updateCachedTheoremData(
                cachedTheorem,
                fileTarget,
                cachedFile.workspacePath,
                cacheUpdaterLogger
            );
        }
    }

    export function buildCachedCoqFileData(
        parsedFileHolder: ParsedFileHolder,
        workspacePath: string,
        cachedFileUpdateLogger: AsOneRecordLogsBuilder
    ): CacheHolderData.CachedCoqFileData {
        const parsedFile = parsedFileHolder.parsedFile();
        const cachedTheoremsMap: Map<
            string,
            CacheHolderData.CachedTheoremData
        > = mapValues(
            parsedFile.theoremsByNames,
            (_, theoremData: TheoremData) =>
                new CacheHolderData.CachedTheoremData(theoremData)
        );
        for (const fileTarget of parsedFileHolder.targets()) {
            const cachedTheorem = cachedTheoremsMap.get(
                fileTarget.sourceTheorem.name
            )!;
            cachedFileUpdateLogger.debug(
                `* cached new theorem: "${fileTarget.sourceTheorem.name}"`
            );
            updateCachedTheoremData(
                cachedTheorem,
                fileTarget,
                workspacePath,
                cachedFileUpdateLogger
            );
        }

        return new CacheHolderData.CachedCoqFileData(
            cachedTheoremsMap,
            relativizeAbsolutePaths(workspacePath, parsedFile.filePath),
            parsedFile.fileLines,
            parsedFile.fileVersion,
            workspacePath
        );
    }

    export function updateCachedTheoremData(
        cachedTheorem: CacheHolderData.CachedTheoremData,
        parsedTarget: ParsedFileTarget,
        workspacePath: string,
        cachedFileUpdateLogger: AsOneRecordLogsBuilder
    ) {
        const cachedTargets = cachedTheorem.getCachedTargetsByType(
            parsedTarget.targetType
        )!;
        const cachedTargetToUpdate = cachedTargets.find((cachedTarget) =>
            parsedTarget.positionRange.equalsTo(cachedTarget.positionRange)
        );
        if (cachedTargetToUpdate === undefined) {
            cachedFileUpdateLogger.debug(
                `** cached new target with goal: ${[parsedTarget.positionRange]}`
            );
            cachedTargets.push(
                new CacheHolderData.CachedTargetData(
                    parsedTarget.goalToProve,
                    parsedTarget.positionRange
                )
            );
        } else {
            cachedFileUpdateLogger.debug(
                `** target goal update: at ${parsedTarget.positionRange.toString()}, was ${cachedTargetToUpdate.hasCachedGoal() ? "defined" : "undefined"}`
            );
            if (cachedTargetToUpdate.hasCachedGoal()) {
                cachedFileUpdateLogger
                    .error(
                        "Cache invariant failed: target was requested, although it was already present in cache"
                    )
                    .debug(
                        `\tTarget info: ${cachedTargetToUpdate.positionRange.toString()} at "${cachedTheorem.theoremData.name}"`
                    );
                throw Error(
                    `Cache invariant failed: most likely, it has become invalid (${workspacePath} project cache)`
                );
            }
            cachedTargetToUpdate.updateWithParsedGoal(parsedTarget.goalToProve);
        }
    }
}
