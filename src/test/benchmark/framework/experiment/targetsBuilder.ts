import {
    TargetType,
    WorkspaceRoot,
} from "../structures/completionGenerationTask";
import {
    getDatasetDir,
    isCoqSourceFile,
    isDirectory,
    joinPaths,
    listCoqSourceFiles,
    resolveAsAbsolutePath,
} from "../utils/fsUtils";
import { getOrPut } from "../utils/mapUtils";

export type InputTargets = WorkspaceToFileTargets;

export type WorkspaceToFileTargets = Map<
    WorkspaceRoot | undefined,
    FilePathToFileTarget
>;

/**
 * File paths are expected to be absolute resolved paths inside `dataset` directory.
 */
export type FilePathToFileTarget = Map<string, FileTarget>;

export interface FileTarget {
    specificTheoremTargets: TheoremNameToTheoremTarget;
    allTheoremsAsAdmitTargets: boolean;
    allTheoremsAsProveTheoremTargets: boolean;
}

export type TheoremNameToTheoremTarget = Map<string, TheoremTarget>;

export interface TheoremTarget {
    admitTargets: boolean;
    proveTheoremTarget: boolean;
}

export type EnvironmentStringType = "nix" | "no-special-environment";

export class TargetsBuilder {
    /**
     * @param directoryPath path relative to the `dataset` directory.
     */
    withWorkspaceRoot(
        directoryPath: string,
        environment: EnvironmentStringType
    ): TargetsBuilderWithWorkspaceRoot {
        let requiresNixEnvironment: boolean;
        switch (environment) {
            case "nix":
                requiresNixEnvironment = true;
                break;
            case "no-special-environment":
                requiresNixEnvironment = false;
                break;
        }
        return new TargetsBuilderWithWorkspaceRoot({
            directoryPath: resolveDatasetPath(directoryPath),
            requiresNixEnvironment: requiresNixEnvironment,
        });
    }

    withoutWorkspaceRoot(): TargetsBuilderWithWorkspaceRoot {
        return new TargetsBuilderWithWorkspaceRoot(undefined);
    }
}

export class TargetsBuilderWithWorkspaceRoot {
    constructor(private readonly workspaceRoot: WorkspaceRoot | undefined) {}

    private readonly inputFileTargets: FilePathToFileTarget = new Map();

    /**
     * @param filePath Coq source file path relative to the `dataset` directory.
     * @param theoremNames names of the theorems inside `filePath`. Leave it empty to select all the theorems.
     */
    withAdmitTargetsFromFile(
        filePath: string,
        ...theoremNames: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromFile(filePath, theoremNames, TargetType.ADMIT);
        return this;
    }

    /**
     * @param filePath Coq source file path relative to the `dataset` directory.
     * @param theoremNames names of the theorems inside `filePath`. Leave it empty to select all the theorems.
     */
    withProveTheoremTargetsFromFile(
        filePath: string,
        ...theoremNames: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromFile(
            filePath,
            theoremNames,
            TargetType.PROVE_THEOREM
        );
        return this;
    }

    /**
     * @param directoryPath directory path relative to the `dataset` directory.
     * @param relativeFilePaths Coq source file paths relative to the `directoryPath`. Leave it empty to select all the source files inside the directory.
     */
    withAdmitTargetsFromDirectory(
        directoryPath: string,
        ...relativeFilePaths: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromDirectory(
            directoryPath,
            relativeFilePaths,
            TargetType.ADMIT
        );
        return this;
    }

    /**
     * @param directoryPath directory path relative to the `dataset` directory.
     * @param relativeFilePaths Coq source file paths relative to the `directoryPath`. Leave it empty to select all the source files inside the directory.
     */
    withProveTheoremTargetsFromDirectory(
        directoryPath: string,
        ...relativeFilePaths: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromDirectory(
            directoryPath,
            relativeFilePaths,
            TargetType.PROVE_THEOREM
        );
        return this;
    }

    buildInputTargets(): InputTargets {
        return new Map([[this.workspaceRoot, this.inputFileTargets]]);
    }

    private withTargetsFromDirectory(
        directoryPath: string,
        relativeFilePaths: string[],
        targetType: TargetType
    ) {
        const resolvedDirectoryPath = resolveDatasetPath(directoryPath);
        if (!isDirectory(resolvedDirectoryPath)) {
            throw Error(
                `resolved path "${directoryPath}" should be a directory: "${resolvedDirectoryPath}"`
            );
        }
        const resolvedDirectoryFilesPaths = listCoqSourceFiles(
            resolvedDirectoryPath
        );
        if (relativeFilePaths.length === 0) {
            resolvedDirectoryFilesPaths.forEach((resolvedFilePath) =>
                this.withTargetsFromResolvedFile(
                    resolvedFilePath,
                    [],
                    targetType
                )
            );
            return;
        }
        const resolvedDirectoryFilesPathsSet = new Set(
            resolvedDirectoryFilesPaths
        );
        for (const relativeFilePath of relativeFilePaths) {
            const resolvedFilePath = resolveDatasetPath(
                joinPaths(directoryPath, relativeFilePath)
            );
            if (!resolvedDirectoryFilesPathsSet.has(resolvedFilePath)) {
                throw Error(
                    `resolved path "${relativeFilePath}" should be a Coq source file inside "${directoryPath}": "${resolvedFilePath}"`
                );
            }
            this.withTargetsFromResolvedFile(resolvedFilePath, [], targetType);
        }
    }

    private withTargetsFromFile(
        relativeFilePath: string,
        theoremNames: string[],
        targetType: TargetType
    ) {
        const resolvedFilePath = resolveDatasetPath(relativeFilePath);
        if (!isCoqSourceFile(resolvedFilePath)) {
            throw Error(
                `resolved path "${relativeFilePath}" should be a Coq source file: "${resolvedFilePath}"`
            );
        }
        this.withTargetsFromResolvedFile(
            resolvedFilePath,
            theoremNames,
            targetType
        );
    }

    private withTargetsFromResolvedFile(
        resolvedFilePath: string,
        theoremNames: string[],
        targetType: TargetType
    ) {
        const fileTarget = getOrPut(
            this.inputFileTargets,
            resolvedFilePath,
            () => {
                return {
                    specificTheoremTargets: new Map(),
                    allTheoremsAsAdmitTargets: false,
                    allTheoremsAsProveTheoremTargets: false,
                };
            }
        );
        if (theoremNames.length === 0) {
            switch (targetType) {
                case TargetType.ADMIT:
                    fileTarget.allTheoremsAsAdmitTargets = true;
                    break;
                case TargetType.PROVE_THEOREM:
                    fileTarget.allTheoremsAsProveTheoremTargets = true;
                    break;
            }
            return;
        }
        for (const theoremName of theoremNames) {
            const theoremTarget = getOrPut(
                fileTarget.specificTheoremTargets,
                theoremName,
                () => {
                    return {
                        admitTargets: false,
                        proveTheoremTarget: false,
                    };
                }
            );
            switch (targetType) {
                case TargetType.ADMIT:
                    theoremTarget.admitTargets = true;
                    break;
                case TargetType.PROVE_THEOREM:
                    theoremTarget.proveTheoremTarget = true;
                    break;
            }
        }
    }
}

/**
 * Merges `multipleInputTargets` into a new `InputTargets` without modifying themselves.
 */
export function mergeInputTargets(
    multipleInputTargets: InputTargets[]
): InputTargets {
    return multipleInputTargets.reduce(
        (acc, inputTargets) => mergeTwoInputTargets(acc, inputTargets),
        new Map()
    );
}

/**
 * Merges `otherInputTargets` into `baseInputTargets`.
 */
function mergeTwoInputTargets(
    baseInputTargets: InputTargets,
    otherInputTargets: InputTargets
): InputTargets {
    for (const [
        workspaceRoot,
        otherFilePathToFileTargets,
    ] of otherInputTargets) {
        const baseFilePathToFileTargets = baseInputTargets.get(workspaceRoot);
        if (baseFilePathToFileTargets === undefined) {
            baseInputTargets.set(workspaceRoot, otherFilePathToFileTargets);
            continue;
        }
        for (const [filePath, otherFileTarget] of otherFilePathToFileTargets) {
            const baseFileTarget = baseFilePathToFileTargets.get(filePath);
            if (baseFileTarget === undefined) {
                baseFilePathToFileTargets.set(filePath, otherFileTarget);
                continue;
            }
            if (otherFileTarget.allTheoremsAsAdmitTargets) {
                baseFileTarget.allTheoremsAsAdmitTargets = true;
            }
            if (otherFileTarget.allTheoremsAsProveTheoremTargets) {
                baseFileTarget.allTheoremsAsProveTheoremTargets = true;
            }
            for (const [
                theoremName,
                otherTheoremTarget,
            ] of otherFileTarget.specificTheoremTargets) {
                const baseTheoremTarget =
                    baseFileTarget.specificTheoremTargets.get(theoremName);
                if (baseTheoremTarget === undefined) {
                    baseFileTarget.specificTheoremTargets.set(
                        theoremName,
                        otherTheoremTarget
                    );
                    continue;
                }
                if (otherTheoremTarget.admitTargets) {
                    baseTheoremTarget.admitTargets = true;
                }
                if (otherTheoremTarget.proveTheoremTarget) {
                    baseTheoremTarget.proveTheoremTarget = true;
                }
            }
        }
    }
    return baseInputTargets;
}

function resolveDatasetPath(inputPath: string): string {
    return resolveAsAbsolutePath(joinPaths(getDatasetDir(), inputPath));
}
