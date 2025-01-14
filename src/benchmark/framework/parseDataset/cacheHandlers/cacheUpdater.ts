import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { ProofStep } from "../../../../coqParser/parsedTypes";
import { toFormattedJsonString } from "../../../../utils/printers";
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

        if (cachedFile.getDocumentVersion() !== parsedFile.documentVersion) {
            cacheUpdaterLogger.debug(
                `* document version update: ${cachedFile.getDocumentVersion()} -> ${parsedFile.documentVersion}`
            );
        }
        cachedFile.updateDocumentVersion(parsedFile.documentVersion);

        const newlyInitializedCachedTheorems = new Set<string>();
        for (const fileTarget of parsedFileHolder.targets()) {
            const theoremName = fileTarget.sourceTheorem.name;
            let cachedTheorem = cachedFile.getCachedTheorem(theoremName);
            if (cachedTheorem === undefined) {
                newlyInitializedCachedTheorems.add(theoremName);
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

            updateCachedTheoremWithRequestedTarget(
                cachedTheorem,
                fileTarget,
                newlyInitializedCachedTheorems.has(theoremName),
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
                    updateCachedTheoremWithRequestedTarget(
                        cachedTheorem,
                        fileTarget,
                        true,
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
            parsedFile.documentVersion,
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
                    `\tTheorem "${cachedTheorem.theoremData.name}" had the following cached targets:\n${toFormattedJsonString(cachedTheorem.targetEntries())}`
                );
            throw Error(
                `Cache building invariant failed: \`CachedTheoremData\` is built incorrectly`
            );
        }

        function initializeCachedTarget(
            targetType: TargetType,
            proofStep: ProofStep,
            knownGoal: ProofGoal | undefined
        ) {
            const cachedTarget = new CacheHolderData.CachedTargetData(
                knownGoal,
                fromRange(proofStep.range)
            );
            cachedTheorem.addCachedTarget(targetType, cachedTarget);
            cachedFileUpdateLogger.debug(
                `  ${
                    knownGoal === undefined
                        ? "** initialized"
                        : "*+ initialized & cached"
                } ${targetType} target: ${[cachedTarget.positionRange]}`
            );
        }

        const sourceTheoremData = cachedTheorem.theoremData;

        // PROVE_THEOREM target
        initializeCachedTarget(
            TargetType.PROVE_THEOREM,
            extractTheoremFisrtProofStep(sourceTheoremData),
            sourceTheoremData.sourceTheorem.initial_goal ?? undefined
        );

        // ADMIT target
        sourceTheoremData.proof?.holes.map((hole) =>
            initializeCachedTarget(TargetType.ADMIT, hole, undefined)
        );
    }

    /**
     * _Note:_ additionally, this method checks two invariants.
     * 1. `CachedTheoremData` should have its targets initialized before updating them with parsed ones.
     * 2. Parsed target should not have been requested, if it had been already present in cache.
     */
    export function updateCachedTheoremWithRequestedTarget(
        cachedTheorem: CacheHolderData.CachedTheoremData,
        parsedTarget: ParsedFileTarget,
        isNewlyInitialized: boolean,
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
                    `\tTheorem "${cachedTheorem.theoremData.name}" had the following cached targets:\n${toFormattedJsonString(cachedTheorem.targetEntries())};`
                )
                .debug(
                    `\t& was going to be updated with ${parsedTarget.targetType} target at ${parsedTarget.positionRange.toString()}`
                );
            throw Error(
                `Cache building invariant failed: \`CachedTheoremData\` is built incorrectly`
            );
        } else {
            const parsedTargetWasBuiltFromInitialGoal =
                parsedTarget.targetType === TargetType.PROVE_THEOREM &&
                parsedTarget.sourceTheorem.sourceTheorem.initial_goal !== null;
            const cachedTargetIsInitializedComplete =
                isNewlyInitialized && parsedTargetWasBuiltFromInitialGoal;
            if (cachedTargetIsInitializedComplete) {
                return;
            }

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
