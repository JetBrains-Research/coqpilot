import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    AllTheoremsTarget,
    FileTarget,
    SpecificTheoremTarget,
    TargetRequestType,
    WorkspaceInputTargets,
} from "../../structures/common/inputTargets";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { DatasetCacheUsageMode } from "../../structures/inputParameters/datasetCaching";
import { ExperimentRunOptions } from "../../structures/inputParameters/experimentRunOptions";
import { all } from "../../utils/collectionUtils/listUtils";
import { listCoqSourceFiles } from "../../utils/fileUtils/fs";
import { readRequestedFilesCache } from "../cacheHandlers/cacheReader";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";
import { createEmptyCache } from "../utils/cacheHoldersUtils";

export function filterRequestedTargetsMissingInCache(
    requestedTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    runOptions: ExperimentRunOptions,
    logger: BenchmarkingLogger
): [WorkspaceInputTargets, WorkspaceCacheHolder] {
    switch (runOptions.datasetCacheUsage) {
        case DatasetCacheUsageMode.NO_CACHE_USAGE:
            return [requestedTargets, createEmptyCache(workspaceRoot)];
        case DatasetCacheUsageMode.READ_CACHE_ONLY:
        case DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS:
            return readCacheAndFilterMissingTargets(
                requestedTargets,
                workspaceRoot,
                runOptions.datasetCacheDirectoryPath,
                logger
            );
        case DatasetCacheUsageMode.REBUILD_CACHE_FOR_REQUESTED_TARGETS:
            return [requestedTargets, createEmptyCache(workspaceRoot)];
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_FILES:
            return [
                CompleteInputTargetsUtils.completeFilesWithAllTargets(
                    requestedTargets
                ),
                createEmptyCache(workspaceRoot),
            ];
        case DatasetCacheUsageMode.REBUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS:
            return [
                CompleteInputTargetsUtils.completeWorkspaceWithAllTargets(
                    workspaceRoot
                ),
                createEmptyCache(workspaceRoot),
            ];
    }
}

function readCacheAndFilterMissingTargets(
    requestedTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    datasetCacheDirectoryPath: string,
    logger: BenchmarkingLogger
): [WorkspaceInputTargets, WorkspaceCacheHolder] {
    const workspaceCache = readRequestedFilesCache(
        requestedTargets.filePaths(),
        workspaceRoot.directoryPath,
        datasetCacheDirectoryPath,
        logger
    );
    const missingTargets = new WorkspaceInputTargets();
    const asOneRecordLogger = logger
        .asOneRecord()
        .debug("Requested targets found in cache:");

    for (const [filePath, fileTargets] of requestedTargets.entries()) {
        let fileCacheIsPresent =
            workspaceCache.getCachedFile(filePath) !== undefined;
        if (fileCacheIsPresent) {
            asOneRecordLogger.debug(`  * file path: ${filePath}`);
        } else {
            asOneRecordLogger.debug(`  ? <missing> file path: ${filePath}`);
        }

        for (const target of fileTargets) {
            let canBeRestoredFromCache = checkTargetCanBeRestored(
                target,
                filePath,
                fileCacheIsPresent,
                workspaceCache,
                workspaceRoot,
                logger
            );
            asOneRecordLogger.debug(
                `${target.toString("    ", canBeRestoredFromCache ? "** (cached)" : "?? <missing>")}`
            );
            if (!canBeRestoredFromCache) {
                addTargetToMissingTargets(target, filePath, missingTargets);
            }
        }
    }

    return [missingTargets, workspaceCache];
}

function checkTargetCanBeRestored(
    target: FileTarget,
    filePath: string,
    fileCacheIsPresent: boolean,
    workspaceCache: WorkspaceCacheHolder,
    workspaceRoot: WorkspaceRoot,
    logger: BenchmarkingLogger
): boolean {
    if (target instanceof AllTheoremsTarget) {
        const allCachedTheorems = workspaceCache.getAllCachedTheorems(filePath);
        return (
            fileCacheIsPresent &&
            all(allCachedTheorems, (cachedTarget) =>
                cachedTarget.hasAllCachedGoalsOfType(target.requestType)
            )
        );
    } else if (target instanceof SpecificTheoremTarget) {
        const cachedTheoremData = workspaceCache.getCachedTheorem(
            filePath,
            target.theoremName
        );
        if (fileCacheIsPresent && cachedTheoremData === undefined) {
            logger
                .asOneRecord()
                .info(
                    `Warning! Either dataset cache for the "${workspaceRoot.directoryPath}" is outdated, or the requested theorem does not exist: `,
                    "yellow",
                    ""
                )
                .info(
                    `theorem "${target.theoremName}" from the ${filePath}`,
                    "yellow"
                );
        }
        return (
            fileCacheIsPresent &&
            cachedTheoremData !== undefined &&
            cachedTheoremData.hasAllCachedGoalsOfType(target.requestType)
        );
    } else {
        throw Error(`Unknown file target: ${stringifyAnyValue(target)}`);
    }
}

function addTargetToMissingTargets(
    target: FileTarget,
    filePath: string,
    missingTargets: WorkspaceInputTargets
) {
    if (target instanceof AllTheoremsTarget) {
        missingTargets.addFileTargets(filePath, [], target.requestType);
    } else if (target instanceof SpecificTheoremTarget) {
        missingTargets.addFileTargets(
            filePath,
            [target.theoremName],
            target.requestType
        );
    } else {
        throw Error(`Unknown file target: ${stringifyAnyValue(target)}`);
    }
}

export namespace CompleteInputTargetsUtils {
    export function completeFilesWithAllTargets(
        requestedTargets: WorkspaceInputTargets
    ): WorkspaceInputTargets {
        const newTargets = new WorkspaceInputTargets();
        newTargets.merge(requestedTargets);
        completeWithAllFileTargets(newTargets, requestedTargets.filePaths());
        return newTargets.resolveRequests();
    }

    export function completeWorkspaceWithAllTargets(
        workspaceRoot: WorkspaceRoot
    ): WorkspaceInputTargets {
        // `isStandaloneFilesRoot` check is not needed: `standaloneFilesRoot` is a separate root
        let filesToRequestPaths = listCoqSourceFiles(
            workspaceRoot.directoryPath
        );

        const newTargets = new WorkspaceInputTargets();
        completeWithAllFileTargets(newTargets, filesToRequestPaths);
        return newTargets.resolveRequests();
    }

    export function completeWithAllFileTargets(
        inputTargets: WorkspaceInputTargets,
        resolvedFilePaths: string[]
    ) {
        for (const filePath of resolvedFilePaths) {
            inputTargets.addFileTargets(
                filePath,
                [],
                TargetRequestType.ALL_ADMITS
            );
            inputTargets.addFileTargets(
                filePath,
                [],
                TargetRequestType.THEOREM_PROOF
            );
        }
    }
}
