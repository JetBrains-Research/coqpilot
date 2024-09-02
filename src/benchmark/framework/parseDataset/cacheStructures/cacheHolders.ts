import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { TargetType } from "../../structures/benchmarkingCore/completionGenerationTask";
import { CodeElementRange } from "../../structures/common/codeElementPositions";
import { TargetRequestType } from "../../structures/common/inputTargets";
import { ParsedCoqFileData } from "../../structures/parsedCoqFile/parsedCoqFileData";
import { TheoremData } from "../../structures/parsedCoqFile/theoremData";
import { all } from "../../utils/collectionUtils/listUtils";
import { mapValues } from "../../utils/collectionUtils/mapUtils";
import { toTargetType } from "../../utils/commonStructuresUtils/targetTypeUtils";
import { joinPaths } from "../../utils/fsUtils";

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

    noCacheFilesRead(): boolean {
        return this.filePathToFileData.size === 0;
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

/**
 * This namespace provides classes to conveniently access the parsing cache.
 * Once the cache is read, these classes should be used instead of `DatasetCacheModels` ones as soon as possible.
 */
export namespace CacheHolderData {
    /**
     * This class represent a cached Coq source file, i.e. its parsing data.
     *
     * **Important invariant:** once a file is cached, it will always contain *all* the theorems
     * present in the original file with *all* the targets present in them (but their cached goals are not guaranteed).
     * In a more practical sense, cached file data can be safely use to determine the presence of the requested theorems and targets
     * (as long as it stays up-to-date with the original file) regardless of the mode and requests that triggered the file cache to be built.
     */
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

    /**
     * This class represent a cached Coq theorem, i.e. its parsing data.
     *
     * **Important invariant:** once a theorem is cached, it will always contain *all* the targets
     * present in its proof (but their goals are not guaranteed to be cached).
     * However, this guarantee requires `CachedTheoremData` to be initialized properly.
     * See its constructor for more details.
     */
    export class CachedTheoremData {
        /**
         * **Build invariant:** when `CachedTheoremData` is built from the parsed theorem,
         * it should be then initialized with `UpdateCacheHolders.buildInitialTargets` function.
         * This function will fill `this.targets` with initial `ADMIT` and `PROVE_THEOREM` targets
         * (without cached goals, just their locations). This approach guarantees that
         * the list of the *present* targets in the cached theorem is up-to-date.
         *
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

        targetEntries(): [TargetType, CacheHolderData.CachedTargetData[]][] {
            return Array.from(this.targets.entries());
        }

        hasNoTargets(): boolean {
            return all(
                Array.from(this.targets.values()),
                (cachedTargets) => cachedTargets.length === 0
            );
        }

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

        addCachedTarget(
            targetType: TargetType,
            cachedTarget: CachedTargetData
        ) {
            this.getCachedTargetsByType(targetType).push(cachedTarget);
        }
    }

    /**
     * This class represent a cached target of a Coq theorem,
     * i.e. parsing data about (potential) target inside a theorem to generate completion for.
     */
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
