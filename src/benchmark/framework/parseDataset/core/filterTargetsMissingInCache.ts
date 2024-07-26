import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../../structures/completionGenerationTask";
import {
    AllTheoremsTarget,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../../structures/inputTargets";
import { all } from "../../utils/listUtils";
import { readRequestedFilesCache } from "../cacheHandlers/cacheReader";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";

// TODO: support caching mode
export function filterRequestedTargetsMissingInCache(
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
    const asOneRecordLogger = logger.asOneRecord();

    for (const [filePath, fileTargets] of requestedTargets.entries()) {
        asOneRecordLogger.debug(`* file path: ${filePath}`);
        for (const target of fileTargets) {
            let canBeRestoredFromCache: boolean;
            if (target instanceof AllTheoremsTarget) {
                canBeRestoredFromCache = all(
                    workspaceCache.getAllCachedTheorems(filePath),
                    (cachedTarget) =>
                        cachedTarget.hasAllCachedGoalsOfType(target.requestType)
                );
                if (!canBeRestoredFromCache) {
                    missingTargets.addFileTargets(
                        filePath,
                        [],
                        target.requestType
                    );
                }
            } else if (target instanceof SpecificTheoremTarget) {
                const cachedTheoremData = workspaceCache.getCachedTheorem(
                    filePath,
                    target.theoremName
                );
                if (cachedTheoremData === undefined) {
                    logger
                        .asOneRecord()
                        .info(
                            `Warning! Either dataset cache for the "${workspaceRoot.directoryPath}" is outdated, or the requested theorem does not exist: `,
                            "yellow"
                        )
                        .info(
                            `theorem "${target.theoremName}" from the ${filePath}`,
                            "yellow"
                        );
                    canBeRestoredFromCache = false;
                } else {
                    canBeRestoredFromCache =
                        cachedTheoremData.hasAllCachedGoalsOfType(
                            target.requestType
                        );
                }
                if (!canBeRestoredFromCache) {
                    missingTargets.addFileTargets(
                        filePath,
                        [target.theoremName],
                        target.requestType
                    );
                }
            } else {
                throw Error(
                    `Unknown file target: ${stringifyAnyValue(target)}`
                );
            }
            asOneRecordLogger.debug(
                `${target.toString("\t", canBeRestoredFromCache ? "+ (cached)" : "- <missing>")}`
            );
        }
    }

    return [missingTargets, workspaceCache];
}
