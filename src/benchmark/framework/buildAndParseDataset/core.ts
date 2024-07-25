import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import {
    AllTheoremsTarget,
    FileTarget,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../structures/inputTargets";
import { buildAndParseCoqProjectInSubprocess } from "../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { all } from "../utils/listUtils";
import { entriesToMappedObject } from "../utils/mapUtils";

import { WorkspaceCacheHolder } from "./cacheHolder";
import { readRequestedFilesCache } from "./cacheReader";
import { ParsedWorkspaceHolder } from "./parsedWorkspaceHolder";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

// TODO: remove export from functions & separate

// 1: Read files from cache
// 2: iterate through requested targets & build
// a) logs on the way, string[] can be built asap
// b) new workspaceItems to request
// !) we are not building results here! for simplicity + same performance
//
// 3: serialize request items
// 4: call parsing, get the results
//
// 5: extend cache with these results
// 6: use these cache RAM structures to build result
// 7: write cache if needed

export function filterRequestedTargetsMissingInCache(
    requestedTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    datasetCacheDirectoryPath: string,
    logger: BenchmarkingLogger
): [WorkspaceInputTargets, WorkspaceCacheHolder] {
    const workspaceCache = readRequestedFilesCache(
        requestedTargets.filePaths(),
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
