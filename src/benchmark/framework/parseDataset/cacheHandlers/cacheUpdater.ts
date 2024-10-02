import { ProofStep } from "../../../../coqParser/parsedTypes";
import { toJsonString } from "../../../../utils/printers";
import {
    AsOneRecordLogsBuilder,
    BenchmarkingLogger,
} from "../../logging/benchmarkingLogger";
import { TargetType } from "../../structures/benchmarkingCore/completionGenerationTask";
import { fromRange } from "../../structures/common/codeElementPositions";
import { TheoremData } from "../../structures/parsedCoqFile/theoremData";
import { groupBy, mapValues } from "../../utils/collectionUtils/mapUtils";
import { extractTheoremFisrtProofStep } from "../../utils/coqUtils/proofTargetExtractor";
import { joinPaths, relativizeAbsolutePaths } from "../../utils/fileUtils/fs";
import {
    CacheHolderData,
    WorkspaceCacheHolder,
} from "../cacheStructures/cacheHolders";
import {
    ParsedFileHolder,
    ParsedFileTarget,
} from "../coqProjectParser/implementation/parsedWorkspaceHolder";

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
            `Update in-memory cache with a new file ${filePath}:`
        );
        workspaceCache.addCachedFile(
            filePath,
            UpdateCacheHolders.buildCachedCoqFileData(
                parsedFileHolder,
                workspaceCache.workspacePath,
                cachedUpdaterLogger
            )
        );
    } else {
        cachedUpdaterLogger.debug(`Update in-memory cache for ${filePath}:`);
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
                cacheUpdaterLogger.debug(
                    `+ cached new theorem: "${fileTarget.sourceTheorem.name}"`
                );
                cachedTheorem = new CacheHolderData.CachedTheoremData(
                    fileTarget.sourceTheorem
                );
                buildInitialTargets(cachedTheorem, cacheUpdaterLogger);
                cachedFile.addCachedTheorem(cachedTheorem);
            } else {
                cacheUpdaterLogger.debug(
                    `* updated theorem: "${fileTarget.sourceTheorem.name}"`
                );
            }

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
        const parsedFileTargetsByTheorem = groupBy(
            parsedFileHolder.targets(),
            (fileTarget) => fileTarget.sourceTheorem.name
        );
        const cachedTheoremsMap: Map<
            string,
            CacheHolderData.CachedTheoremData
        > = mapValues(
            parsedFile.theoremsByNames,
            (_, theoremData: TheoremData) => {
                cachedFileUpdateLogger.debug(
                    `+ cached new theorem: "${theoremData.name}"`
                );
                const cachedTheorem = new CacheHolderData.CachedTheoremData(
                    theoremData
                );
                buildInitialTargets(cachedTheorem, cachedFileUpdateLogger);

                for (const fileTarget of parsedFileTargetsByTheorem.get(
                    theoremData.name
                ) ?? []) {
                    updateCachedTheoremData(
                        cachedTheorem,
                        fileTarget,
                        workspacePath,
                        cachedFileUpdateLogger
                    );
                }
                return cachedTheorem;
            }
        );
        return new CacheHolderData.CachedCoqFileData(
            cachedTheoremsMap,
            relativizeAbsolutePaths(workspacePath, parsedFile.filePath),
            parsedFile.fileLines,
            parsedFile.fileVersion,
            workspacePath
        );
    }

    export function buildInitialTargets(
        cachedTheorem: CacheHolderData.CachedTheoremData,
        cachedFileUpdateLogger: AsOneRecordLogsBuilder
    ) {
        if (!cachedTheorem.hasNoTargets()) {
            cachedFileUpdateLogger
                .error(
                    "Cache building invariant failed: `CachedTheoremData` should have no targets before their initial build"
                )
                .debug(
                    `\tTheorem "${cachedTheorem.theoremData.name}" had the following cached targets:\n${toJsonString(cachedTheorem.targetEntries(), 2)}`
                );
            throw Error(
                `Cache building invariant failed: \`CachedTheoremData\` is built incorrectly`
            );
        }
        const sourceTheoremData = cachedTheorem.theoremData;
        const sourceTargets = new Map<TargetType, ProofStep[]>([
            [
                TargetType.PROVE_THEOREM,

                [extractTheoremFisrtProofStep(sourceTheoremData)],
            ],
            [TargetType.ADMIT, sourceTheoremData.proof?.holes ?? []],
        ]);

        for (const [targetType, targetsOfType] of sourceTargets) {
            targetsOfType
                .map(
                    (proofStep) =>
                        new CacheHolderData.CachedTargetData(
                            undefined,
                            fromRange(proofStep.range)
                        )
                )
                .forEach((cachedTarget) => {
                    cachedTheorem.addCachedTarget(targetType, cachedTarget);
                    cachedFileUpdateLogger.debug(
                        `  ** initialized ${targetType} target: ${[cachedTarget.positionRange]}`
                    );
                });
        }
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
            cachedFileUpdateLogger
                .error(
                    "Cache building invariant failed: `CachedTheoremData` should have initialized targets before updating them with parsed ones"
                )
                .debug(
                    `\tTheorem "${cachedTheorem.theoremData.name}" had the following cached targets:\n${toJsonString(cachedTheorem.targetEntries(), 2)};`
                )
                .debug(
                    `\t& was going to be updated with ${parsedTarget.targetType} target at ${parsedTarget.positionRange.toString()}`
                );
            throw Error(
                `Cache building invariant failed: \`CachedTheoremData\` is built incorrectly`
            );
        } else {
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
            cachedFileUpdateLogger.debug(
                `  ++ cached goal for ${parsedTarget.targetType} target at ${parsedTarget.positionRange.toString()}`
            );
        }
    }
}
