import { getDatasetDir, joinPaths } from "../../utils/fsUtils";

export interface WorkspaceRoot {
    /**
     * This path is expected to be an absolute resolved path inside the `dataset` directory.
     */
    directoryPath: string;
    requiresNixEnvironment: boolean;
}

/**
 * Relative to the `dataset` directory.
 */
const standaloneFilesRootRelativePath = "standalone-source-files";

/**
 * Mock `WorkspaceRoot` for standalone target files that do not have an actual workspace.
 * Its `directoryPath` points to the `standaloneFilesRootRelativePath` inside the `dataset` directory,
 * where such files are expected to be stored.
 *
 * When working with `WorkspaceRoot` object, it should be checked via `isStandaloneFilesRoot` function.
 * In case it is indeed this mock `standaloneFilesRoot`, it should be handled as a special case.
 *
 * Implementation note: `standaloneFilesRoot` was chosen instead of `undefined` due to
 * its better support as a key of `Map` and general convenience of paths resolving.
 */
export const standaloneFilesRoot: WorkspaceRoot = {
    directoryPath: joinPaths(getDatasetDir(), standaloneFilesRootRelativePath),
    requiresNixEnvironment: false,
};

export function isStandaloneFilesRoot(workspaceRoot: WorkspaceRoot): boolean {
    return workspaceRoot === standaloneFilesRoot;
}
