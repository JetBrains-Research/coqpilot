import { stringifyAnyValue } from "../../../../utils/printers";
import {
    EqualTo,
    EqualitySet,
    HashUtils,
} from "../../utils/collectionUtils/equalitySet";
import { getOrPut } from "../../utils/collectionUtils/mapUtils";
import { toTargetType } from "../../utils/commonStructuresUtils/targetTypeUtils";
import { TargetType } from "../benchmarkingCore/completionGenerationTask";

import { WorkspaceRoot } from "./workspaceRoot";

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

    isEmpty(): boolean {
        for (const workspaceTargets of this.workspacePathToTargets.values()) {
            if (!workspaceTargets.isEmpty()) {
                return false;
            }
        }
        return true;
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
     * Merges `other` into `this`. Resulting internal structures of `other` and `this`
     * are guaranteed to be distinct. In other words, any further modification of `other`
     * will not affect `this` and vice versa.
     *
     * *Implementation note:* the independency of `DatasetInputTargets` is guaranteed by usage of
     * separate internal structures (`workspacePathToTargets` map and its `WorkspaceInputTargets` values)
     * and by `WorkspaceInputTargets.merge(...)` invariant. See its docs for more details.
     */
    merge(other: DatasetInputTargets) {
        for (const [
            workspacePath,
            otherWorkspaceTargets,
        ] of other.workspacePathToTargets.entries()) {
            const thisWorkspaceTargets = getOrPut(
                this.workspacePathToTargets,
                workspacePath,
                () => {
                    this.workspacePathToRoots.set(
                        workspacePath,
                        other.workspacePathToRoots.get(workspacePath)!
                    );
                    return new WorkspaceInputTargets();
                }
            );
            thisWorkspaceTargets.merge(otherWorkspaceTargets);
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
                `- workspace: ${workspacePath}\n${targets.toString("  ")}`
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

    isEmpty(): boolean {
        for (const fileTargets of this.filePathToTargets.values()) {
            if (!fileTargets.isEmpty()) {
                return false;
            }
        }
        return true;
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
     * Merges `other` into `this`. Resulting internal structures of `other` and `this`
     * are guaranteed to be distinct. In other words, any further modification of `other`
     * will not affect `this` and vice versa.
     *
     * *Implementaiton note:* to guarantee `this` and `other` independency, `filePathToTargets` map
     * and each of its `EqualitySet<FileTargets>` structures are created separately for both `WorkspaceInputTargets`.
     * However, `FileTargets` objects used might still be the same: but it does not break the invariant, since they are immutable.
     */
    merge(other: WorkspaceInputTargets) {
        for (const [filePath, otherFileTargets] of other.filePathToTargets) {
            const thisFileTargets = getOrPut(
                this.filePathToTargets,
                filePath,
                () => new EqualitySet()
            );
            thisFileTargets.addElements(otherFileTargets.elements());
        }
    }

    /**
     * Resolves file targets sets for each of the file paths:
     * if `AllTheoremsTarget` is present, all corresponding `SpecificTheoremTarget`-s will be removed.
     *
     * @returns this.
     */
    resolveRequests(): WorkspaceInputTargets {
        for (const [filePath, targets] of this.filePathToTargets) {
            const resolvedRequest = new Map<TargetType, FileTarget[]>();

            for (const target of targets.elements()) {
                if (target instanceof AllTheoremsTarget) {
                    resolvedRequest.set(toTargetType(target.requestType), [
                        target,
                    ]);
                } else if (target instanceof SpecificTheoremTarget) {
                    const requestsOfSameTargetType = getOrPut(
                        resolvedRequest,
                        toTargetType(target.requestType),
                        () => [] as FileTarget[]
                    );
                    const allTheoremsTargetIsPresent =
                        requestsOfSameTargetType.length === 1 &&
                        requestsOfSameTargetType[0] instanceof
                            AllTheoremsTarget;
                    if (!allTheoremsTargetIsPresent) {
                        requestsOfSameTargetType.push(target);
                    }
                } else {
                    throw Error(
                        `unknown \`FileTarget\` type: ${stringifyAnyValue(target)}`
                    );
                }
            }

            this.filePathToTargets.set(
                filePath,
                new EqualitySet(Array.from(resolvedRequest.values()).flat())
            );
        }
        return this;
    }

    toString(linePrefix: string = ""): string {
        const elements = [];
        for (const [filePath, targets] of this.filePathToTargets) {
            const targetsString = targets
                .elements()
                .map((target) => target.toString("    ", "**"))
                .join("\n");
            elements.push(`${linePrefix}* file: ${filePath}\n${targetsString}`);
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
