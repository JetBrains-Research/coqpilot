import { EqualTo, EqualitySet, HashUtils } from "../utils/equalitySet";
import { getOrPut } from "../utils/mapUtils";

import { WorkspaceRoot } from "./completionGenerationTask";

/**
 * Merges `DatasetInputTargets`-s into a new `DatasetInputTargets` without modifying themselves.
 */
export function mergeInputTargets(
    multipleDatasetInputTargets: DatasetInputTargets[]
): DatasetInputTargets {
    const mergeBase = new DatasetInputTargets();
    for (const targets of multipleDatasetInputTargets) {
        mergeBase.merge(targets);
    }
    return mergeBase;
}

export class DatasetInputTargets {
    private readonly workspacePathToTargets: Map<
        string,
        WorkspaceInputTargets
    > = new Map();
    private readonly workspacePathToRoots: Map<string, WorkspaceRoot> =
        new Map();

    workspacesNumber(): number {
        return this.workspacePathToTargets.size;
    }

    entries(): [WorkspaceRoot, WorkspaceInputTargets][] {
        const entries: [WorkspaceRoot, WorkspaceInputTargets][] = [];
        for (const [
            workspacePath,
            targets,
        ] of this.workspacePathToTargets.entries()) {
            entries.push([
                this.workspacePathToRoots.get(workspacePath)!,
                targets,
            ]);
        }
        return entries;
    }

    addWorkspaceTargets(
        workspaceRoot: WorkspaceRoot,
        workspaceTargets: WorkspaceInputTargets
    ): DatasetInputTargets {
        this.workspacePathToTargets.set(
            workspaceRoot.directoryPath,
            workspaceTargets
        );
        this.workspacePathToRoots.set(
            workspaceRoot.directoryPath,
            workspaceRoot
        );
        return this;
    }

    /**
     * Merges `other` into `this`.
     */
    merge(other: DatasetInputTargets) {
        for (const [
            workspacePath,
            targets,
        ] of other.workspacePathToTargets.entries()) {
            if (this.workspacePathToTargets.has(workspacePath)) {
                this.workspacePathToTargets.get(workspacePath)!.merge(targets);
            } else {
                this.workspacePathToTargets.set(workspacePath, targets);
                this.workspacePathToRoots.set(
                    workspacePath,
                    other.workspacePathToRoots.get(workspacePath)!
                );
            }
        }
    }

    /**
     * Removes repetitive requests of internal file targets.
     *
     * Example: "all admits of all theorems" includes "all admits from theorem X";
     * therefore, the latter should be removed.
     *
     * @returns this.
     */
    resolveRequests(): DatasetInputTargets {
        for (const targets of this.workspacePathToTargets.values()) {
            targets.resolveRequests();
        }
        return this;
    }

    toString(): string {
        const elements = [];
        for (const [workspacePath, targets] of this.workspacePathToTargets) {
            elements.push(
                `* workspace: ${workspacePath}\n${targets.toString("\t")}`
            );
        }
        return elements.join("\n");
    }
}

export class WorkspaceInputTargets {
    /**
     * File paths are expected to be absolute resolved paths inside `dataset` directory.
     */
    private readonly filePathToTargets: Map<string, EqualitySet<FileTarget>> =
        new Map();

    entries(): [string, FileTarget[]][] {
        const entries: [string, FileTarget[]][] = [];
        for (const [filePath, targets] of this.filePathToTargets.entries()) {
            entries.push([filePath, targets.elements()]);
        }
        return entries;
    }

    filePaths(): string[] {
        return Array.from(this.filePathToTargets.keys());
    }

    /**
     * If `theoremNames` is empty, `AllTheoremsTarget` is added.
     * Otherwise, `SpecificTheoremTarget` for each theorem name is added.
     */
    addFileTargets(
        resolvedFilePath: string,
        theoremNames: string[],
        requestType: TargetRequestType
    ) {
        const targets = getOrPut(
            this.filePathToTargets,
            resolvedFilePath,
            () => new EqualitySet<FileTarget>()
        );
        if (theoremNames.length === 0) {
            targets.add(new AllTheoremsTarget(requestType));
        } else {
            targets.addElements(
                theoremNames.map(
                    (theoremName) =>
                        new SpecificTheoremTarget(theoremName, requestType)
                )
            );
        }
    }

    /**
     * Merges `other` into `this`.
     */
    merge(other: WorkspaceInputTargets) {
        for (const [filePath, targets] of other.filePathToTargets) {
            if (this.filePathToTargets.has(filePath)) {
                this.filePathToTargets
                    .get(filePath)!
                    .addElements(targets.elements());
            } else {
                this.filePathToTargets.set(filePath, targets);
            }
        }
    }

    /**
     * Resolves file targets sets for each of the file paths:
     * if `AllTheoremsTarget` is present, all corresponding `SpecificTheoremTarget`-s will be removed.
     */
    resolveRequests() {
        for (const [filePath, targets] of this.filePathToTargets) {
            const allTheoremsRequests = new Map<
                TargetRequestType,
                AllTheoremsTarget
            >();
            for (const target of targets.elements()) {
                if (target instanceof AllTheoremsTarget) {
                    allTheoremsRequests.set(target.requestType, target);
                }
            }
            if (allTheoremsRequests.size === 0) {
                return;
            }
            this.filePathToTargets.set(
                filePath,
                new EqualitySet(Array.from(allTheoremsRequests.values()))
            );
        }
    }

    toString(linePrefix: string = ""): string {
        const elements = [];
        for (const [filePath, targets] of this.filePathToTargets) {
            const targetsString = targets
                .elements()
                .map((target) => target.toString("\t\t", "-"))
                .join("\n");
            elements.push(`${linePrefix}- file: ${filePath}\n${targetsString}`);
        }
        return elements.join("\n");
    }
}

export abstract class FileTarget implements EqualTo<FileTarget> {
    abstract equalTo(other: FileTarget): boolean;
    abstract hash(): number;
    abstract toString(linePrefix: string, itemizeString: string): string;
}

export class SpecificTheoremTarget extends FileTarget {
    constructor(
        readonly theoremName: string,
        readonly requestType: TargetRequestType
    ) {
        super();
    }

    equalTo(other: FileTarget): boolean {
        return (
            other instanceof SpecificTheoremTarget &&
            other.theoremName === this.theoremName &&
            other.requestType === this.requestType
        );
    }

    hash(): number {
        return HashUtils.hashAsStrings(
            this.theoremName,
            this.requestType,
            "SpecificTheoremTarget"
        );
    }

    toString(linePrefix: string = "", itemizeString: string = "-"): string {
        return `${linePrefix}${itemizeString} theorem "${this.theoremName}", ${this.requestType}`;
    }
}

export class AllTheoremsTarget extends FileTarget {
    constructor(readonly requestType: TargetRequestType) {
        super();
    }

    equalTo(other: FileTarget): boolean {
        return (
            other instanceof AllTheoremsTarget &&
            other.requestType === this.requestType
        );
    }

    hash(): number {
        return HashUtils.hashAsStrings(this.requestType, "AllTheoremsTarget");
    }

    toString(linePrefix: string = "", itemizeString: string = "-"): string {
        return `${linePrefix}${itemizeString} all theorems, ${this.requestType}`;
    }
}

export enum TargetRequestType {
    ALL_ADMITS = "ALL_ADMITS",
    THEOREM_PROOF = "THEOREM_PROOF",
}
