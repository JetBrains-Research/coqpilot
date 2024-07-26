import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { updateWorkspaceCache } from "../cacheHandlers/cacheUpdater";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";
import { ParsedWorkspaceHolder } from "../coqProjectParser/parsedWorkspaceHolder";

// TODO: support caching mode
export function extendCacheWithParsedTargets(
    workspaceCache: WorkspaceCacheHolder,
    parsedWorkspace: ParsedWorkspaceHolder,
    logger: BenchmarkingLogger
) {
    for (const [filePath, parsedFileHolder] of parsedWorkspace.entries()) {
        updateWorkspaceCache(
            workspaceCache,
            filePath,
            parsedFileHolder,
            logger
        );
    }
    logger.info(
        `Successfully updated cache for ${workspaceCache.workspacePath} workspace: ${parsedWorkspace.parsedFilesNumber()} files updated`
    );
    // TODO: debug log full cache?
}
