import { ModelParams } from "../../../llm/llmServices/modelParams";
import { resolveOrThrow } from "../../../llm/llmServices/utils/resolveOrThrow";

import { stringifyAnyValue } from "../../../utils/printers";
import { InputBenchmarkingModelParams } from "../experiment/inputBenchmarkingModelParams";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { BenchmarkingModelParams } from "../structures/benchmarkingModelParams";
import {
    CompletionGenerationTask,
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../structures/experimentRunOptions";
import { InputBenchmarkingBundle } from "../structures/inputBenchmarkingBundle";
import {
    AllTheoremsTarget,
    DatasetInputTargets,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../structures/inputTargets";
import { LLMServiceIdentifier } from "../structures/llmServiceIdentifier";
import { ParsedCoqFileData } from "../structures/parsedCoqFileData";
import { buildAndParseCoqProjectInSubprocess } from "../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";
import { AsyncScheduler } from "../utils/asyncScheduler";
import { EqualitySet } from "../utils/equalitySet";
import { all } from "../utils/listUtils";
import {
    LLMServicesParamsResolvers,
    createParamsResolvers,
    getParamsResolver,
} from "../utils/llmServicesUtils";
import { entriesToMappedObject, getOrPut } from "../utils/mapUtils";
import { resolveTheoremsRanker } from "../utils/resolveTheoremsRanker";
import { toTargetType } from "../utils/targetTypeUtils";

import {
    CacheHolderData,
    DatasetCacheHolder,
    WorkspaceCacheHolder,
} from "./cacheHolder";
import { readRequestedFilesCache } from "./cacheReader";
import { updateWorkspaceCache } from "./cacheUpdater";
import { ParsedWorkspaceHolder } from "./parsedWorkspaceHolder";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

// TODO: remove export from functions & separate
// TODO: add constructed benchmarking items logs

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

// TODO: support caching mode
export function extendCacheWithParsedTargets(
    workspaceCache: WorkspaceCacheHolder,
    parsedWorkspace: ParsedWorkspaceHolder,
    logger: BenchmarkingLogger
) {
    for (const [filePath, parsedFileHolder] of parsedWorkspace.entries()) {
        updateWorkspaceCache(
            workspaceCache,
            filePath,
            parsedFileHolder,
            logger
        );
    }
    logger.info(
        `Successfully updated cache for ${workspaceCache.workspacePath} workspace: ${parsedWorkspace.parsedFilesNumber()} files updated`
    );
    // TODO: debug log full cache?
}

export function constructBenchmarkingItems(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder
): BenchmarkingItem[] {
    const [modelIdToRequestedTasks, modelIdToResolvedParams] =
        buildTasksAndResolveParams(inputBundles, datasetCache);

    return buildBenchmarkingItems(
        modelIdToRequestedTasks,
        modelIdToResolvedParams
    );
}

function buildTasksAndResolveParams(
    inputBundles: InputBenchmarkingBundle[],
    datasetCache: DatasetCacheHolder
): [
    Map<string, CompletionGenerationTask[]>,
    Map<string, BenchmarkingModelParams<ModelParams>>,
] {
    const modelIdToRequestedTasks: Map<string, CompletionGenerationTask[]> =
        new Map();
    const modelIdToResolvedParams: Map<
        string,
        BenchmarkingModelParams<ModelParams>
    > = new Map();
    const paramsResolvers = createParamsResolvers();

    for (const bundle of inputBundles) {
        const bundleTasks: CompletionGenerationTask[] =
            constructTasksForBundleTargets(
                bundle.requestedTargets,
                datasetCache
            );

        // Attach constructed `bundleTasks` to all models requested in the bundle.
        for (const inputParams of bundle.inputBenchmarkingModelsParams) {
            const modelId = inputParams.modelId;
            const requestedTasks = getOrPut(
                modelIdToRequestedTasks,
                modelId,
                () => {
                    // If this model is met for the first time: resolve its parameters.
                    modelIdToResolvedParams.set(
                        modelId,
                        resolveInputBenchmarkingModelParams(
                            inputParams,
                            bundle.llmServiceIdentifier,
                            paramsResolvers
                        )
                    );
                    return [] as CompletionGenerationTask[];
                }
            );
            requestedTasks.push(...bundleTasks);
        }
    }
    return [modelIdToRequestedTasks, modelIdToResolvedParams];
}

function buildBenchmarkingItems(
    modelIdToRequestedTasks: Map<string, CompletionGenerationTask[]>,
    modelIdToResolvedParams: Map<string, BenchmarkingModelParams<ModelParams>>
): BenchmarkingItem[] {
    const benchmarkingItems: BenchmarkingItem[] = [];
    for (const [modelId, requestedTasks] of modelIdToRequestedTasks.entries()) {
        const uniqueTasks = new EqualitySet<CompletionGenerationTask>(
            requestedTasks
        ).elements();

        for (const task of uniqueTasks) {
            benchmarkingItems.push({
                task: task,
                params: modelIdToResolvedParams.get(modelId)!,
            });
        }
    }
    return benchmarkingItems;
}

function resolveInputBenchmarkingModelParams(
    inputParams: InputBenchmarkingModelParams.Params,
    llmServiceIdentifier: LLMServiceIdentifier,
    paramsResolvers: LLMServicesParamsResolvers
): BenchmarkingModelParams<ModelParams> {
    const paramsResolver = getParamsResolver(
        llmServiceIdentifier,
        paramsResolvers
    );
    const { ranker, ...pureInputModelParams } = inputParams;
    return {
        theoremRanker: resolveTheoremsRanker(inputParams.ranker),
        modelParams: resolveOrThrow(paramsResolver, pureInputModelParams),
        llmServiceIdentifier: llmServiceIdentifier,
    };
}

export function constructTasksForBundleTargets(
    requestedTargets: DatasetInputTargets,
    datasetCache: DatasetCacheHolder
): CompletionGenerationTask[] {
    const bundleTasks: CompletionGenerationTask[] = [];

    for (const [
        workspaceRoot,
        workspaceTargets,
    ] of requestedTargets.entries()) {
        const workspaceCache = datasetCache.getWorkspaceCache(
            workspaceRoot.directoryPath
        );
        if (workspaceCache === undefined) {
            throwInsufficientCacheError(
                `workspace ${workspaceRoot.directoryPath}`
            );
        }

        for (const [filePath, fileTargets] of workspaceTargets.entries()) {
            const cachedFile = workspaceCache.getCachedFile(filePath);
            if (cachedFile === undefined) {
                throwInsufficientCacheError(`file ${filePath}`);
            }
            const parsedFileData = cachedFile.restoreParsedCoqFileData();

            for (const fileTarget of fileTargets) {
                if (fileTarget instanceof AllTheoremsTarget) {
                    for (const cachedTheorem of cachedFile.getAllCachedTheorems()) {
                        bundleTasks.push(
                            ...constructTasksForTargetsFromTheorem(
                                cachedTheorem,
                                fileTarget,
                                parsedFileData,
                                workspaceRoot
                            )
                        );
                    }
                } else if (fileTarget instanceof SpecificTheoremTarget) {
                    const cachedTheorem = cachedFile.getCachedTheorem(
                        fileTarget.theoremName
                    );
                    if (cachedTheorem === undefined) {
                        throwInsufficientCacheError(
                            `theorem ${fileTarget.theoremName} from ${filePath}`
                        );
                    }
                    bundleTasks.push(
                        ...constructTasksForTargetsFromTheorem(
                            cachedTheorem,
                            fileTarget,
                            parsedFileData,
                            workspaceRoot
                        )
                    );
                } else {
                    throw Error(
                        `Unknown file target: ${fileTarget.toString("", "")}`
                    );
                }
            }
        }
    }

    return bundleTasks;
}

function constructTasksForTargetsFromTheorem(
    cachedTheorem: CacheHolderData.CachedTheoremData,
    fileTarget: AllTheoremsTarget | SpecificTheoremTarget,
    parsedFileData: ParsedCoqFileData,
    workspaceRoot: WorkspaceRoot
): CompletionGenerationTask[] {
    return cachedTheorem
        .getCachedTargetsByRequestType(fileTarget.requestType)
        .map((cachedTarget) => {
            const goalToProve = cachedTarget.getGoalToProve();
            const targetType = toTargetType(fileTarget.requestType);
            if (goalToProve === undefined) {
                throwInsufficientCacheError(
                    `"${targetType}" target at ${cachedTarget.positionRange.toString()} of theorem ${cachedTheorem.theoremData.name} from ${parsedFileData.filePath}`
                );
            }
            return new CompletionGenerationTask(
                goalToProve,
                cachedTarget.positionRange,
                targetType,
                parsedFileData,
                cachedTheorem.theoremData,
                workspaceRoot
            );
        });
}

function throwInsufficientCacheError(missingObject: string): never {
    const errorMessageLines = [
        "Failed to build benchmarking items: ",
        "invariant failed, updated cache is not sufficient to process requested targets.",
        `\n\tCause: ${missingObject} data is missing.`,
    ];
    throw Error(errorMessageLines.join(""));
}
