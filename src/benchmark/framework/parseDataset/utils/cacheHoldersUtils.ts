import { WorkspaceRoot } from "../../structures/workspaceRoot";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";

export function createEmptyCache(
    workspaceRoot: WorkspaceRoot
): WorkspaceCacheHolder {
    return new WorkspaceCacheHolder(workspaceRoot.directoryPath);
}
