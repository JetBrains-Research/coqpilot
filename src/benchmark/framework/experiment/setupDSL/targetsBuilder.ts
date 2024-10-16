import {
    DatasetInputTargets,
    TargetRequestType,
    WorkspaceInputTargets,
} from "../../structures/common/inputTargets";
import {
    WorkspaceRoot,
    standaloneFilesRoot,
} from "../../structures/common/workspaceRoot";
import {
    getDatasetDir,
    isCoqSourceFile,
    isDirectory,
    joinPaths,
    listCoqSourceFiles,
    resolveAsAbsolutePath,
} from "../../utils/fileUtils/fs";

export type EnvironmentStringType = "nix" | "no-special-environment";

export class TargetsBuilder {
    /**
     * @param directoryPath path relative to the `dataset` directory.
     */
    withWorkspaceRoot(
        directoryPath: string,
        environment: EnvironmentStringType
    ): TargetsBuilderWithWorkspaceRoot {
        return new TargetsBuilderWithWorkspaceRoot(
            TargetsBuilderUtils.buildWorkspaceRoot(directoryPath, environment)
        );
    }

    /**
     * Standalone dataset source files are expected to be found
     * in the `dataset/standalone-source-files` directory.
     */
    withStandaloneFilesRoot(): TargetsBuilderWithWorkspaceRoot {
        return new TargetsBuilderWithWorkspaceRoot(standaloneFilesRoot);
    }
}

export class TargetsBuilderWithWorkspaceRoot {
    constructor(private readonly workspaceRoot: WorkspaceRoot) {}

    private readonly workspaceTargets = new WorkspaceInputTargets();

    /**
     * @param filePath Coq source file path relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
     * @param theoremNames names of the theorems inside `filePath`. Leave it empty to select all the theorems.
     */
    withAdmitTargetsFromFile(
        filePath: string,
        ...theoremNames: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromFile(
            filePath,
            theoremNames,
            TargetRequestType.ALL_ADMITS
        );
        return this;
    }

    /**
     * @param filePath Coq source file path relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
     * @param theoremNames names of the theorems inside `filePath`. Leave it empty to select all the theorems.
     */
    withProveTheoremTargetsFromFile(
        filePath: string,
        ...theoremNames: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromFile(
            filePath,
            theoremNames,
            TargetRequestType.THEOREM_PROOF
        );
        return this;
    }

    /**
     * @param directoryPath directory path relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
     * @param relativeFilePaths Coq source file paths relative to the `directoryPath`. Leave it empty to select all the source files inside the directory.
     */
    withAdmitTargetsFromDirectory(
        directoryPath: string,
        ...relativeFilePaths: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromDirectory(
            directoryPath,
            relativeFilePaths,
            TargetRequestType.ALL_ADMITS
        );
        return this;
    }

    /**
     * @param directoryPath directory path relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
     * @param relativeFilePaths Coq source file paths relative to the `directoryPath`. Leave it empty to select all the source files inside the directory.
     */
    withProveTheoremTargetsFromDirectory(
        directoryPath: string,
        ...relativeFilePaths: string[]
    ): TargetsBuilderWithWorkspaceRoot {
        this.withTargetsFromDirectory(
            directoryPath,
            relativeFilePaths,
            TargetRequestType.THEOREM_PROOF
        );
        return this;
    }

    buildInputTargets(): DatasetInputTargets {
        return new DatasetInputTargets().addWorkspaceTargets(
            this.workspaceRoot,
            this.workspaceTargets
        );
    }

    private withTargetsFromDirectory(
        directoryPath: string,
        relativeFilePaths: string[],
        requestType: TargetRequestType
    ) {
        const resolvedDirectoryPath = TargetsBuilderUtils.resolveWorkspacePath(
            this.workspaceRoot,
            directoryPath
        );
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
                    requestType
                )
            );
            return;
        }
        const resolvedDirectoryFilesPathsSet = new Set(
            resolvedDirectoryFilesPaths
        );
        for (const relativeFilePath of relativeFilePaths) {
            const resolvedFilePath = TargetsBuilderUtils.resolveDatasetPath(
                joinPaths(directoryPath, relativeFilePath)
            );
            if (!resolvedDirectoryFilesPathsSet.has(resolvedFilePath)) {
                throw Error(
                    `resolved path "${relativeFilePath}" should be a Coq source file inside "${directoryPath}": "${resolvedFilePath}"`
                );
            }
            this.withTargetsFromResolvedFile(resolvedFilePath, [], requestType);
        }
    }

    private withTargetsFromFile(
        relativeFilePath: string,
        theoremNames: string[],
        requestType: TargetRequestType
    ) {
        const resolvedFilePath = TargetsBuilderUtils.resolveWorkspacePath(
            this.workspaceRoot,
            relativeFilePath
        );
        if (!isCoqSourceFile(resolvedFilePath)) {
            throw Error(
                `resolved path "${relativeFilePath}" should be a Coq source file: "${resolvedFilePath}"`
            );
        }
        this.withTargetsFromResolvedFile(
            resolvedFilePath,
            theoremNames,
            requestType
        );
    }

    private withTargetsFromResolvedFile(
        resolvedFilePath: string,
        theoremNames: string[],
        requestType: TargetRequestType
    ) {
        this.workspaceTargets.addFileTargets(
            resolvedFilePath,
            theoremNames,
            requestType
        );
    }
}

export namespace TargetsBuilderUtils {
    export function buildWorkspaceRoot(
        directoryPath: string,
        environment: EnvironmentStringType
    ): WorkspaceRoot {
        let requiresNixEnvironment: boolean;
        switch (environment) {
            case "nix":
                requiresNixEnvironment = true;
                break;
            case "no-special-environment":
                requiresNixEnvironment = false;
                break;
        }
        return {
            directoryPath: resolveDatasetPath(directoryPath),
            requiresNixEnvironment: requiresNixEnvironment,
        };
    }

    export function resolveWorkspacePath(
        workspaceRoot: WorkspaceRoot,
        inputPath: string
    ): string {
        return resolveAsAbsolutePath(
            joinPaths(workspaceRoot.directoryPath, inputPath)
        );
    }

    export function resolveDatasetPath(inputPath: string): string {
        return resolveAsAbsolutePath(joinPaths(getDatasetDir(), inputPath));
    }
}
