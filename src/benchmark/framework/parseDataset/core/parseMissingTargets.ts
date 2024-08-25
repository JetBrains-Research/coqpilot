import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/inputTargets";
import { WorkspaceRoot } from "../../structures/workspaceRoot";
import { updateWorkspaceCache } from "../cacheHandlers/cacheUpdater";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";
import { AbstractCoqProjectParser } from "../coqProjectParser/abstractCoqProjectParser";
import { ParsedWorkspaceHolder } from "../coqProjectParser/parsedWorkspaceHolder";

export async function parseMissingTargetsAndUpdateCache(
    missingTargets: WorkspaceInputTargets,
    workspaceCacheToUpdate: WorkspaceCacheHolder,
    workspaceRoot: WorkspaceRoot,
    logger: BenchmarkingLogger,
    parser: AbstractCoqProjectParser
) {
    const parsedWorkspace = await parser.parseCoqProject(
        missingTargets,
        workspaceRoot,
        logger
    );
    updateCacheWithParsedTargets(
        workspaceCacheToUpdate,
        parsedWorkspace,
        logger
    );
}

function updateCacheWithParsedTargets(
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
    logger.debug(
        `Successfully updated in-memory cache for ${workspaceCache.workspacePath} workspace: ${parsedWorkspace.parsedFilesNumber()} file(s) updated`
    );
}
