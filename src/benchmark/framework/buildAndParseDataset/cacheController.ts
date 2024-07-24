import { Goal, PpString } from "../../../coqLsp/coqLspTypes";

import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import {
    TargetType,
    WorkspaceRoot,
} from "../structures/completionGenerationTask";
import { TheoremData, deserializeTheorem } from "../structures/theoremData";
import { deserializeCodeElementRange } from "../structures/utilStructures";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";
import { joinPaths } from "../utils/fsUtils";
import { all } from "../utils/listUtils";

import { DatasetCacheModels } from "./cacheModels";
import { readRequestedFilesCache } from "./cacheReader";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

// TODO ~ Signature.ArgsModels.FilePathToFileTarget:
// use `Map` instead of object keys for file targets until the moment to pass it to child process

export function retrieveRequestedTargetsFromCache(
    workspaceRoot: WorkspaceRoot,
    requestedFileTargets: Signature.ArgsModels.FilePathToFileTarget,
    datasetCacheDirectoryPath: string,
    logger: BenchmarkingLogger
) {
    const cachedCoqFilesByNames = readRequestedFilesCache(
        Object.keys(requestedFileTargets),
        datasetCacheDirectoryPath,
        logger
    );
    const fileTargetsToParse = new FileTargetsToParseBuilder();
    const logsBuilder = new CacheControllerLogs.LogsBuilder(
        requestedFileTargets
    );
    const restoredResult = new RestoredFromCacheResultBuilder(logsBuilder);

    // TODO: implement key-value object `entries()` util
    for (const filePath of Object.keys(requestedFileTargets)) {
        const fileTarget = requestedFileTargets[filePath];

        const cachedFile = cachedCoqFilesByNames.get(filePath);
        if (cachedFile === undefined) {
            fileTargetsToParse.addCompleteFileTarget(filePath, fileTarget);
            continue;
        }

        handleSpecificTheoremTargets(
            fileTarget,
            cachedFile,
            fileTargetsToParse,
            restoredResult,
            filePath,
            workspaceRoot,
            logger
        );
        // TODO: handle all theorem targets

        fileTargetsToParse.buildCurrentFileTarget(filePath);
        restoredResult.buildCurrentFileTarget(
            filePath,
            cachedFile,
            workspaceRoot
        );
    }
}

function handleSpecificTheoremTargets(
    fileTarget: Signature.ArgsModels.FileTarget,
    cachedFile: DatasetCacheModels.CachedCoqFile,
    fileTargetsToParse: FileTargetsToParseBuilder,
    restoredResult: RestoredFromCacheResultBuilder,
    filePath: string,
    workspaceRoot: WorkspaceRoot,
    logger: BenchmarkingLogger
) {
    for (const theoremName of Object.keys(fileTarget.specificTheoremTargets)) {
        const theoremTarget = fileTarget.specificTheoremTargets[theoremName];

        const cachedTheorem = cachedFile.allFileTheorems[theoremName];
        if (cachedTheorem === undefined) {
            logger
                .asOneRecord()
                .info(
                    `Warning! Either dataset cache for the "${workspaceRoot.directoryPath}" is outdated, or the requested theorem does not exist: `,
                    "yellow"
                )
                .info(
                    `theorem "${theoremName}" from the ${filePath}`,
                    "yellow"
                );
            fileTargetsToParse.addCompleteTheoremTarget(
                theoremName,
                theoremTarget
            );
            continue;
        }

        const requestedTheoremTargets =
            fileTarget.specificTheoremTargets[theoremName];
        for (const requestedTargetType of Object.keys(
            requestedTheoremTargets
        ) as Signature.CommonModels.TargetType[]) {
            const requestedBundleIds =
                requestedTheoremTargets[requestedTargetType];
            let cached = false;
            switch (requestedTargetType) {
                case "ADMIT":
                    cached = all(
                        cachedTheorem.admitTargets,
                        (cachedTarget) => cachedTarget.goalToProve !== undefined
                    );
                    break;
                case "PROVE_THEOREM":
                    cached =
                        cachedTheorem.proofTarget.goalToProve !== undefined;
                    break;
            }
            if (cached) {
                restoredResult.addExtractedTaskTargetsOfType(
                    requestedTargetType,
                    cachedTheorem,
                    requestedBundleIds,
                    filePath
                );
            } else {
                fileTargetsToParse.addTargetTypeBundles(
                    requestedTargetType,
                    requestedBundleIds
                );
            }
        }
        fileTargetsToParse.buildCurrentTheoremTarget(theoremName);
    }
}

namespace CacheControllerLogs {
    export class LogsBuilder {
        private readonly requestedFileTargetsStatus: Map<
            string,
            FileTargetLog
        > = new Map();

        constructor(
            requestedFileTargets: Signature.ArgsModels.FilePathToFileTarget
        ) {
            for (const filePath of Object.keys(requestedFileTargets)) {
                const theoremTargetsRestored = new Map<
                    TheoremNameWithTargetType,
                    boolean
                >();
                const requestedTheoremTargets =
                    requestedFileTargets[filePath].specificTheoremTargets;
                for (const theoremName of Object.keys(
                    requestedTheoremTargets
                )) {
                    for (const targetType of Object.keys(
                        requestedTheoremTargets[theoremName]
                    )) {
                        theoremTargetsRestored.set(
                            {
                                theoremName: theoremName,
                                targetType:
                                    targetType as Signature.CommonModels.TargetType,
                            },
                            false
                        );
                    }
                }
                this.requestedFileTargetsStatus.set(filePath, {
                    specificTheoremTargetsRestored: theoremTargetsRestored,
                    allTheoremsAdmitsRestored: false,
                    allTheoremsProofsRestored: false,
                });
            }
        }

        markTaskTargetRestored(
            filePath: string,
            theoremName: string,
            targetType: Signature.CommonModels.TargetType
        ) {
            const fileTarget = this.requestedFileTargetsStatus.get(filePath)!;
            fileTarget.specificTheoremTargetsRestored.set(
                {
                    theoremName: theoremName,
                    targetType: targetType,
                },
                true
            );
        }
    }

    interface FileTargetLog {
        specificTheoremTargetsRestored: Map<TheoremNameWithTargetType, boolean>;
        allTheoremsAdmitsRestored: boolean;
        allTheoremsProofsRestored: boolean;
    }

    interface TheoremNameWithTargetType {
        theoremName: string;
        targetType: Signature.CommonModels.TargetType;
    }
}

class FileTargetsToParseBuilder {
    private readonly fileTargets: Signature.ArgsModels.FilePathToFileTarget =
        {};

    private currentFileTarget: Signature.ArgsModels.FileTarget = {
        specificTheoremTargets: {},
        allTheoremsTargetTypes: {
            ADMIT: [],
            PROVE_THEOREM: [],
        },
    };

    private currentTheoremTarget: Signature.ArgsModels.TheoremTarget = {
        ADMIT: [],
        PROVE_THEOREM: [],
    };

    addCompleteFileTarget(
        filePath: string,
        fileTarget: Signature.ArgsModels.FileTarget
    ) {
        this.fileTargets[filePath] = fileTarget;
    }

    addCompleteTheoremTarget(
        theoremName: string,
        theoremTarget: Signature.ArgsModels.TheoremTarget
    ) {
        this.currentFileTarget.specificTheoremTargets[theoremName] =
            theoremTarget;
    }

    addTargetTypeBundles(
        targetType: Signature.CommonModels.TargetType,
        requestedBundleIds: number[]
    ) {
        this.currentTheoremTarget[targetType] = requestedBundleIds;
    }

    buildCurrentFileTarget(filePath: string) {
        this.fileTargets[filePath] = this.currentFileTarget;
        this.currentFileTarget = {
            specificTheoremTargets: {},
            allTheoremsTargetTypes: {
                ADMIT: [],
                PROVE_THEOREM: [],
            },
        };
    }

    buildCurrentTheoremTarget(theoremName: string) {
        this.currentFileTarget.specificTheoremTargets[theoremName] =
            this.currentTheoremTarget;
        this.currentTheoremTarget = {
            ADMIT: [],
            PROVE_THEOREM: [],
        };
    }
}

class RestoredFromCacheResultBuilder {
    private readonly result: Signature.UnpackedResultModels.UnpackedResult =
        new Map();

    private currentTaskTargets: Signature.UnpackedResultModels.TaskTarget[] =
        [];

    constructor(
        private readonly logsBuilder: CacheControllerLogs.LogsBuilder
    ) {}

    addExtractedTaskTargetsOfType(
        targetType: Signature.CommonModels.TargetType,
        cachedTheorem: DatasetCacheModels.CachedTheorem,
        requestedBundleIds: number[],
        filePath: string // TODO: get rid of, not it is here only because of logger flow
    ) {
        const sourceTheorem = new TheoremData(
            deserializeTheorem(cachedTheorem.theorem)
        );
        let cachedTargetsOfType: DatasetCacheModels.CachedTarget[] = [];
        let extractedTargetType: TargetType;
        switch (targetType) {
            case "ADMIT":
                cachedTargetsOfType = cachedTheorem.admitTargets;
                extractedTargetType = TargetType.ADMIT;
                break;
            case "PROVE_THEOREM":
                cachedTargetsOfType = [cachedTheorem.proofTarget];
                extractedTargetType = TargetType.PROVE_THEOREM;
                break;
        }
        for (const cachedTarget of cachedTargetsOfType) {
            this.currentTaskTargets.push({
                targetGoalToProve: JSON.parse(
                    cachedTarget.goalToProve!
                ) as Goal<PpString>,
                targetPositionRange: deserializeCodeElementRange(
                    cachedTarget.positionRange
                ),
                targetType: extractedTargetType,
                sourceTheorem: sourceTheorem,
                bundleIds: new Set(requestedBundleIds),
            });
        }
        this.logsBuilder.markTaskTargetRestored(
            filePath,
            sourceTheorem.name,
            targetType
        );
    }

    buildCurrentFileTarget(
        filePath: string,
        cachedFile: DatasetCacheModels.CachedCoqFile,
        workspaceRoot: WorkspaceRoot
    ) {
        this.result.set(filePath, {
            parsedFile: {
                allFileTheorems: Object.values(cachedFile.allFileTheorems).map(
                    (cachedTheorem) =>
                        new TheoremData(
                            deserializeTheorem(cachedTheorem.theorem)
                        )
                ),
                fileLines: cachedFile.fileLines, // TODO: update after parsing request
                fileVersion: cachedFile.fileVersion, // TODO: update after parsing request
                filePath: joinPaths(
                    workspaceRoot.directoryPath,
                    cachedFile.filePathRelativeToWorkspace
                ),
            },
            extractedTaskTargets: this.currentTaskTargets,
        });
        this.currentTaskTargets = [];
    }
}
