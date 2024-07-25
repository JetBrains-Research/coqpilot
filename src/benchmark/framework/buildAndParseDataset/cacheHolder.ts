import { TargetRequestType } from "../structures/inputTargets";
import { SerializedTheorem } from "../structures/theoremData";
import { SerializedCodeElementRange } from "../structures/utilStructures";
import { all } from "../utils/listUtils";

import { DatasetCacheModels } from "./cacheModels";

export class DatasetCacheHolder {
    private readonly workspacePathToFiles: Map<string, WorkspaceCacheHolder> =
        new Map();

    addWorkspaceCache(
        workspacePath: string,
        workspaceCache: WorkspaceCacheHolder
    ) {
        this.workspacePathToFiles.set(workspacePath, workspaceCache);
    }
}

export class WorkspaceCacheHolder {
    private readonly filePathToFileData: Map<
        string,
        CacheHolderData.CachedCoqFileData
    >;

    constructor(
        filePathToReadCachedFile: Map<string, DatasetCacheModels.CachedCoqFile>
    ) {
        this.filePathToFileData = new Map(
            Array.from(filePathToReadCachedFile.entries()).map(
                ([filePath, readCachedFile]) => [
                    filePath,
                    CacheHolderData.CachedCoqFileData.buildFrom(readCachedFile),
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

        static buildFrom(
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
                    CachedTheoremData.buildFrom(readCachedTheorem)
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
         * @param targets should always have entries for all `TargetRequestType`-s, at least empty lists.
         */
        constructor(
            private readonly theorem: SerializedTheorem,
            private readonly targets: Map<TargetRequestType, CachedTargetData[]>
        ) {}

        hasAllCachedGoalsOfType(requestType: TargetRequestType): boolean {
            return all(this.targets.get(requestType)!, (cachedTarget) =>
                cachedTarget.hasCachedGoal()
            );
        }

        static buildFrom(
            readCachedTheorem: DatasetCacheModels.CachedTheorem
        ): CachedTheoremData {
            return new CachedTheoremData(
                readCachedTheorem.theorem,
                new Map<TargetRequestType, CachedTargetData[]>([
                    [
                        TargetRequestType.THEOREM_PROOF,
                        [
                            CachedTargetData.buildFrom(
                                readCachedTheorem.proofTarget
                            ),
                        ],
                    ],
                    [
                        TargetRequestType.ALL_ADMITS,
                        readCachedTheorem.admitTargets.map((admitTarget) =>
                            CachedTargetData.buildFrom(admitTarget)
                        ),
                    ],
                ])
            );
        }
    }

    export class CachedTargetData {
        constructor(
            private goalToProve: DatasetCacheModels.ParsedGoal | undefined,
            private readonly positionRange: SerializedCodeElementRange
        ) {}

        static buildFrom(
            readCachedTarget: DatasetCacheModels.CachedTarget
        ): CachedTargetData {
            return new CachedTargetData(
                readCachedTarget.goalToProve,
                readCachedTarget.positionRange
            );
        }

        hasCachedGoal(): boolean {
            return this.goalToProve !== undefined;
        }
    }
}
