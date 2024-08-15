import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { CompleteInputTargetsUtils } from "../parseDataset/core/filterTargetsMissingInCache";
import {
    DatasetInputTargets,
    WorkspaceInputTargets,
    mergeInputTargets,
} from "../structures/inputTargets";
import {
    WorkspaceRoot,
    standaloneFilesRoot,
} from "../structures/workspaceRoot";
import { isDirectory, listCoqSourceFiles } from "../utils/fsUtils";

import { EnvironmentStringType, TargetsBuilderUtils } from "./targetsBuilder";

export namespace DatasetCacheBuilderImpl {
    /**
     * Builds dataset cache for the requested targets.
     * The returning promise resolves successfully if and only if the operation succeeded.
     */
    export async function buildDatasetCache(
        cacheTargetsBuilders: CacheTargets.CacheTargetsBuilder[],
        logger: BenchmarkingLogger
    ) {
        const cacheTargets = mergeInputTargets(
            cacheTargetsBuilders.map((builder) => builder.buildCacheTargets())
        ).resolveRequests();
        if (cacheTargets.isEmpty()) {
            throw Error(
                "No targets for building dataset cache were selected. Configure some and try again."
            );
        }
        logger.debug(`Cache targets:\n${cacheTargets.toString()}`);

        // TODO: build cache + save it
    }
}

export namespace CacheTargets {
    /**
     * A builder for the workspace targets to be parsed and cached.
     *
     * `files(...)` or `directories(...)` calls can be used to select specific files to cache.
     * If no such calls are made, the final `buildCacheTargets()` method
     * will request all source files inside the workspace to be cached.
     */
    export class CacheTargetsBuilder {
        private readonly workspaceTargets = new WorkspaceInputTargets();

        constructor(private readonly workspaceRoot: WorkspaceRoot) {}

        /**
         * @param filePaths Coq source file paths relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
         */
        files(...filePaths: string[]): CacheTargetsBuilder {
            const resolvedFilePaths = filePaths.map((filePath) =>
                TargetsBuilderUtils.resolveWorkspacePath(
                    this.workspaceRoot,
                    filePath
                )
            );
            this.completeWithAllFileTargets(resolvedFilePaths);
            return this;
        }

        /**
         * @param directoryPaths directory paths relative to the workspace directory (or to the `dataset/standalone-source-files` directory for standalone files).
         */
        directories(...directoryPaths: string[]): CacheTargetsBuilder {
            const resolvedDirectoryPaths = directoryPaths.map((directoryPath) =>
                TargetsBuilderUtils.resolveWorkspacePath(
                    this.workspaceRoot,
                    directoryPath
                )
            );
            const resolvedFilePaths = resolvedDirectoryPaths.flatMap(
                (resolvedDirectoryPath) => {
                    if (!isDirectory(resolvedDirectoryPath)) {
                        throw Error(
                            `Building dataset cache target is invalid: resolved path "${resolvedDirectoryPath}" should be a directory`
                        );
                    }
                    return listCoqSourceFiles(resolvedDirectoryPath);
                }
            );
            this.completeWithAllFileTargets(resolvedFilePaths);
            return this;
        }

        buildCacheTargets(): DatasetInputTargets {
            if (this.workspaceTargets.isEmpty()) {
                // if neither `files(...)` nor `directories(...)` were called, all workspace sources should be added
                this.completeWithAllFileTargets(
                    listCoqSourceFiles(this.workspaceRoot.directoryPath)
                );
            }
            /**
             * Note: `this.workspaceTargets.resolveRequests()` is not needed here,
             * since all `DatasetInputTargets` produced by all `CacheTargetsBuilder` requested
             * will be resolved all together later.
             */
            return new DatasetInputTargets().addWorkspaceTargets(
                this.workspaceRoot,
                this.workspaceTargets
            );
        }

        private completeWithAllFileTargets(resolvedFilePaths: string[]) {
            // Note: explicit duplicates filtering is not needed here, since `WorkspaceInputTargets` handles them by itself
            CompleteInputTargetsUtils.completeWithAllFileTargets(
                this.workspaceTargets,
                resolvedFilePaths
            );
        }
    }

    /**
     * Specifies a dataset workspace to parse and cache.
     * If `workspace(...)` is followed by `files(...)` or `directories(...)` calls,
     * only specified files will be cached. Otherwise, all source files inside the workspace will be cached.
     *
     * @param directoryPath path relative to the `dataset` directory.
     */
    export function workspace(
        directoryPath: string,
        environment: EnvironmentStringType
    ): CacheTargetsBuilder {
        return new CacheTargetsBuilder(
            TargetsBuilderUtils.buildWorkspaceRoot(directoryPath, environment)
        );
    }

    /**
     * Specifies a standalone dataset files root (`dataset/standalone-source-files`) to parse and cache.
     * If `standaloneFiles(...)` is followed by `files(...)` or `directories(...)` calls,
     * only specified files will be cached. Otherwise, all standalone dataset source files will be cached.
     */
    export function standaloneFiles(): CacheTargetsBuilder {
        return new CacheTargetsBuilder(standaloneFilesRoot);
    }
}
