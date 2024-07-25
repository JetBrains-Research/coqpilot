import { ProofGoal } from "../../../coqLsp/coqLspTypes";

import {
    AsOneRecordLogsBuilder,
    BenchmarkingLogger,
} from "../logging/benchmarkingLogger";
import { TargetType } from "../structures/completionGenerationTask";
import { TargetRequestType } from "../structures/inputTargets";
import { TheoremData, deserializeTheoremData } from "../structures/theoremData";
import {
    CodeElementRange,
    deserializeCodeElementRange,
} from "../structures/utilStructures";
import { joinPaths, relativizeAbsolutePaths } from "../utils/fsUtils";
import { deserializeGoal } from "../utils/goalParser";
import { all } from "../utils/listUtils";
import { getOrPut, mapValues } from "../utils/mapUtils";
import { toTargetType } from "../utils/targetTypeUtils";

import { DatasetCacheModels } from "./cacheModels";
import { ParsedFileHolder, ParsedFileTarget } from "./parsedWorkspaceHolder";

export class WorkspaceCacheHolder {
    private readonly filePathToFileData: Map<
        string,
        CacheHolderData.CachedCoqFileData
    >;

    constructor(
        filePathToReadCachedFile: Map<string, DatasetCacheModels.CachedCoqFile>,
        readonly workspacePath: string
    ) {
        this.filePathToFileData = new Map(
            Array.from(filePathToReadCachedFile.entries()).map(
                ([filePath, readCachedFile]) => [
                    filePath,
                    CacheHolderData.CachedCoqFileData.buildFromReadCache(
                        readCachedFile
                    ),
                ]
            )
        );
    }

    getCachedTheorem(
        filePath: string,
        theoremName: string
    ): CacheHolderData.CachedTheoremData | undefined {
        return this.filePathToFileData
            .get(filePath)
            ?.getCachedTheorem(theoremName);
    }

    getAllCachedTheorems(
        filePath: string
    ): CacheHolderData.CachedTheoremData[] {
        return (
            this.filePathToFileData.get(filePath)?.getAllCachedTheorems() ?? []
        );
    }

    updateWithParsedTargets(
        filePath: string,
        parsedFileHolder: ParsedFileHolder,
        logger: BenchmarkingLogger
    ) {
        const cachedFileUpdateLogger = logger.asOneRecord();

        const cachedFile = this.filePathToFileData.get(filePath);
        if (cachedFile === undefined) {
            cachedFileUpdateLogger.debug(`Cache ${filePath}:`);
            this.filePathToFileData.set(
                filePath,
                CacheHolderData.CachedCoqFileData.buildFromParsedTargets(
                    parsedFileHolder,
                    this.workspacePath,
                    cachedFileUpdateLogger
                )
            );
            cachedFileUpdateLogger.debug("");
        } else {
            cachedFileUpdateLogger.debug(`Update cache for ${filePath}:`);
            cachedFile.updateWithParsedTargets(
                parsedFileHolder,
                this.workspacePath,
                cachedFileUpdateLogger
            );
        }
    }
}

export namespace CacheHolderData {
    export class CachedCoqFileData {
        constructor(
            private readonly theorems: Map<string, CachedTheoremData>,
            private readonly filePathRelativeToWorkspace: string,
            private fileLines: string[],
            private fileVersion: number
        ) {}

        getCachedTheorem(theoremName: string): CachedTheoremData | undefined {
            return this.theorems.get(theoremName);
        }

        getAllCachedTheorems(): CachedTheoremData[] {
            return Array.from(this.theorems.values());
        }

        updateWithParsedTargets(
            parsedFileHolder: ParsedFileHolder,
            workspacePath: string,
            cachedFileUpdateLogger: AsOneRecordLogsBuilder
        ) {
            const parsedFile = parsedFileHolder.parsedFile();
            const cachedResolvedPath = joinPaths(
                workspacePath,
                this.filePathRelativeToWorkspace
            );
            if (cachedResolvedPath !== parsedFile.filePath) {
                cachedFileUpdateLogger
                    .error(
                        "\nCache invariant failed: parsed targets file path is different from already cached one"
                    )
                    .debug(
                        `\tCause: cached file path ${cachedResolvedPath} != parsed file path ${parsedFile.filePath}`
                    );
                throw Error(
                    `Cache invariant failed: most likely, it has become invalid (${workspacePath} project cache)`
                );
            }

            if (this.fileVersion !== parsedFile.fileVersion) {
                cachedFileUpdateLogger.debug(
                    `* file version update: ${this.fileVersion} -> ${parsedFile.fileVersion}`
                );
            }
            this.fileLines = parsedFile.fileLines;
            this.fileVersion = parsedFile.fileVersion;

            for (const fileTarget of parsedFileHolder.targets()) {
                let newTheorem = false;
                const cachedTheorem = getOrPut(
                    this.theorems,
                    fileTarget.sourceTheorem.name,
                    () => {
                        newTheorem = true;
                        return new CacheHolderData.CachedTheoremData(
                            fileTarget.sourceTheorem
                        );
                    }
                );
                cachedFileUpdateLogger.debug(
                    `* ${newTheorem ? "cached new" : "updated"} theorem: "${fileTarget.sourceTheorem.name}"`
                );
                cachedTheorem.updateWithParsedTarget(
                    fileTarget,
                    workspacePath,
                    cachedFileUpdateLogger
                );
            }
        }

        static buildFromParsedTargets(
            parsedFileHolder: ParsedFileHolder,
            workspacePath: string,
            cachedFileUpdateLogger: AsOneRecordLogsBuilder
        ): CachedCoqFileData {
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
                cachedTheorem.updateWithParsedTarget(
                    fileTarget,
                    workspacePath,
                    cachedFileUpdateLogger
                );
            }

            return new CacheHolderData.CachedCoqFileData(
                cachedTheoremsMap,
                relativizeAbsolutePaths(workspacePath, parsedFile.filePath),
                parsedFile.fileLines,
                parsedFile.fileVersion
            );
        }

        static buildFromReadCache(
            readCachedFile: DatasetCacheModels.CachedCoqFile
        ): CachedCoqFileData {
            const theorems = new Map();
            for (const theoremName of Object.keys(
                readCachedFile.allFileTheorems
            )) {
                const readCachedTheorem =
                    readCachedFile.allFileTheorems[theoremName];
                theorems.set(
                    theoremName,
                    CachedTheoremData.buildFromReadCache(readCachedTheorem)
                );
            }
            return new CachedCoqFileData(
                theorems,
                readCachedFile.filePathRelativeToWorkspace,
                readCachedFile.fileLines,
                readCachedFile.fileVersion
            );
        }
    }

    export class CachedTheoremData {
        /**
         * @param targets should always have entries for all `TargetType`-s, at least empty lists.
         */
        constructor(
            private readonly theorem: TheoremData,
            private readonly targets: Map<
                TargetType,
                CachedTargetData[]
            > = new Map([
                [TargetType.ADMIT, []],
                [TargetType.PROVE_THEOREM, []],
            ])
        ) {}

        hasAllCachedGoalsOfType(requestType: TargetRequestType): boolean {
            return all(
                this.targets.get(toTargetType(requestType))!,
                (cachedTarget) => cachedTarget.hasCachedGoal()
            );
        }

        updateWithParsedTarget(
            parsedTarget: ParsedFileTarget,
            workspacePath: string,
            cachedFileUpdateLogger: AsOneRecordLogsBuilder
        ) {
            const cachedTargets = this.targets.get(parsedTarget.targetType)!;
            const cachedTargetToUpdate = cachedTargets.find((cachedTarget) =>
                parsedTarget.positionRange.equalsTo(cachedTarget.positionRange)
            );
            if (cachedTargetToUpdate === undefined) {
                cachedFileUpdateLogger.debug(
                    `** cached new target with goal: at ${[parsedTarget.positionRange]}`
                );
                cachedTargets.push(
                    new CachedTargetData(
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
                            `\tTarget info: ${cachedTargetToUpdate.positionRange.toString()} at "${this.theorem.name}"`
                        );
                    throw Error(
                        `Cache invariant failed: most likely, it has become invalid (${workspacePath} project cache)`
                    );
                }
                cachedTargetToUpdate.updateWithParsedGoal(
                    parsedTarget.goalToProve
                );
            }
        }

        static buildFromReadCache(
            readCachedTheorem: DatasetCacheModels.CachedTheorem
        ): CachedTheoremData {
            return new CachedTheoremData(
                deserializeTheoremData(readCachedTheorem.theorem),
                new Map<TargetType, CachedTargetData[]>([
                    [
                        TargetType.PROVE_THEOREM,
                        [
                            CachedTargetData.buildFromReadCache(
                                readCachedTheorem.proofTarget
                            ),
                        ],
                    ],
                    [
                        TargetType.ADMIT,
                        readCachedTheorem.admitTargets.map((admitTarget) =>
                            CachedTargetData.buildFromReadCache(admitTarget)
                        ),
                    ],
                ])
            );
        }
    }

    export class CachedTargetData {
        constructor(
            private goalToProve: ProofGoal | undefined,
            readonly positionRange: CodeElementRange
        ) {}

        hasCachedGoal(): boolean {
            return this.goalToProve !== undefined;
        }

        updateWithParsedGoal(goalToProve: ProofGoal) {
            this.goalToProve = goalToProve;
        }

        static buildFromReadCache(
            readCachedTarget: DatasetCacheModels.CachedTarget
        ): CachedTargetData {
            return new CachedTargetData(
                readCachedTarget.goalToProve === undefined
                    ? undefined
                    : deserializeGoal(readCachedTarget.goalToProve),
                deserializeCodeElementRange(readCachedTarget.positionRange)
            );
        }
    }
}
