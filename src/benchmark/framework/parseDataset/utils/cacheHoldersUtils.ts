import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";

export function createEmptyCache(
    workspaceRoot: WorkspaceRoot
): WorkspaceCacheHolder {
    return new WorkspaceCacheHolder(workspaceRoot.directoryPath);
}
