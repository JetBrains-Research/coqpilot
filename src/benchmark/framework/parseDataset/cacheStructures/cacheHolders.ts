import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { TargetType } from "../../structures/completionGenerationTask";
import { TargetRequestType } from "../../structures/inputTargets";
import { ParsedCoqFileData } from "../../structures/parsedCoqFileData";
import { TheoremData } from "../../structures/theoremData";
import { CodeElementRange } from "../../structures/utilStructures";
import { joinPaths } from "../../utils/fsUtils";
import { all } from "../../utils/listUtils";
import { mapValues } from "../../utils/mapUtils";
import { toTargetType } from "../../utils/targetTypeUtils";

export class DatasetCacheHolder {
    private readonly workspacePathToCache: Map<string, WorkspaceCacheHolder> =
        new Map();

    entries(): [string, WorkspaceCacheHolder][] {
        return Array.from(this.workspacePathToCache.entries());
    }

    getWorkspaceCache(workspacePath: string): WorkspaceCacheHolder | undefined {
        return this.workspacePathToCache.get(workspacePath);
    }

    addWorkspaceCache(
        workspacePath: string,
        workspaceCache: WorkspaceCacheHolder
    ) {
        this.workspacePathToCache.set(workspacePath, workspaceCache);
    }
}

export class WorkspaceCacheHolder {
    constructor(
        readonly workspacePath: string,
        private readonly filePathToFileData: Map<
            string,
            CacheHolderData.CachedCoqFileData
        > = new Map()
    ) {}

    entries(): [string, CacheHolderData.CachedCoqFileData][] {
        return Array.from(this.filePathToFileData.entries());
    }

    getCachedFile(
        filePath: string
    ): CacheHolderData.CachedCoqFileData | undefined {
        return this.filePathToFileData.get(filePath);
    }

    getAllCachedTheorems(
        filePath: string
    ): CacheHolderData.CachedTheoremData[] {
        return this.getCachedFile(filePath)?.getAllCachedTheorems() ?? [];
    }

    getCachedTheorem(
        filePath: string,
        theoremName: string
    ): CacheHolderData.CachedTheoremData | undefined {
        return this.getCachedFile(filePath)?.getCachedTheorem(theoremName);
    }

    addCachedFile(
        filePath: string,
        cachedFile: CacheHolderData.CachedCoqFileData
    ) {
        this.filePathToFileData.set(filePath, cachedFile);
    }
}

export namespace CacheHolderData {
    export class CachedCoqFileData {
        constructor(
            private readonly theorems: Map<string, CachedTheoremData>,
            readonly filePathRelativeToWorkspace: string,
            private fileLines: string[],
            private fileVersion: number,
            readonly workspacePath: string
        ) {}

        getAllCachedTheorems(): CachedTheoremData[] {
            return Array.from(this.theorems.values());
        }

        getCachedTheorem(theoremName: string): CachedTheoremData | undefined {
            return this.theorems.get(theoremName);
        }

        getFileLines(): string[] {
            return this.fileLines;
        }

        getFileVersion(): number {
            return this.fileVersion;
        }

        addCachedTheorem(cachedTheorem: CachedTheoremData) {
            this.theorems.set(cachedTheorem.theoremData.name, cachedTheorem);
        }

        updateFileLines(fileLines: string[]) {
            this.fileLines = fileLines;
        }

        updateFileVersion(fileVersion: number) {
            this.fileVersion = fileVersion;
        }

        restoreParsedCoqFileData(): ParsedCoqFileData {
            return new ParsedCoqFileData(
                mapValues(
                    this.theorems,
                    (_: string, cachedTheorem: CachedTheoremData) =>
                        cachedTheorem.theoremData
                ),
                this.fileLines,
                this.fileVersion,
                joinPaths(this.workspacePath, this.filePathRelativeToWorkspace)
            );
        }
    }

    export class CachedTheoremData {
        /**
         * @param targets should always have entries for all `TargetType`-s, at least empty lists.
         */
        constructor(
            readonly theoremData: TheoremData,
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

        getCachedTargetsByRequestType(
            requestType: TargetRequestType
        ): CachedTargetData[] {
            return this.getCachedTargetsByType(toTargetType(requestType));
        }

        getCachedTargetsByType(targetType: TargetType): CachedTargetData[] {
            return this.targets.get(targetType)!;
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

        getGoalToProve(): ProofGoal | undefined {
            return this.goalToProve;
        }

        updateWithParsedGoal(goalToProve: ProofGoal) {
            this.goalToProve = goalToProve;
        }
    }
}
