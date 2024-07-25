import { stringifyAnyValue } from "../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import {
    AllTheoremsTarget,
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

export async function parseCoqProjectForMissingTargets(
    missingTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: AsyncScheduler,
    logger: BenchmarkingLogger
): Promise<ParsedWorkspaceHolder> {
    const executionResult = await buildAndParseCoqProjectInSubprocess(
        workspaceRoot,
        packWorspaceTargets(missingTargets),
        false, // TODO: support turning projects building on
        runOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
        subprocessesScheduler,
        logger,
        runOptions.enableSubprocessLifetimeDebugLogs
    );
    const projectId = isNoWorkspaceRoot(workspaceRoot)
        ? "standalone source files requested"
        : `"${workspaceRoot.directoryPath}" project with source files requested`;
    if (executionResult.isFailed()) {
        logger
            .asOneRecord()
            .error(`failed to build and parse ${projectId}`, undefined, "")
            .debug(`: ${missingTargets.filePaths().join(", ")}`, undefined, "")
            .error(
                `\n\tcaused by \`${executionResult.errorTypeName}\`: ${executionResult.errorMessage}`
            );
        throw Error("failed to build benchmarking items");
    }
    const parsedWorkspaceHolder = executionResult.maybeResult!;
    logger.info(
        `Successfully parsed ${projectId}: ${parsedWorkspaceHolder.parsedFilesNumber()} files`
    );
    return parsedWorkspaceHolder;
}

export function packWorspaceTargets(
    missingTargets: WorkspaceInputTargets
): Signature.ArgsModels.FilePathToFileTargets {
    const mappedEntries: [string, Signature.ArgsModels.FileTarget[]][] =
        missingTargets.entries().map(([filePath, fileTargets]) => {
            return [
                filePath,
                fileTargets.map((fileTarget) => {
                    if (fileTarget instanceof AllTheoremsTarget) {
                        return {
                            requestType: fileTarget.requestType,
                            specificTheoremName: undefined,
                        };
                    } else if (fileTarget instanceof SpecificTheoremTarget) {
                        return {
                            requestType: fileTarget.requestType,
                            specificTheoremName: fileTarget.theoremName,
                        };
                    } else {
                        throw Error(
                            `Unknown input file target: ${fileTarget.toString("", "")}`
                        );
                    }
                }),
            ];
        });
    return entriesToMappedObject(mappedEntries);
}
