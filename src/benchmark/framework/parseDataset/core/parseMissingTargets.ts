import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { ExperimentRunOptions } from "../../structures/experimentRunOptions";
import { WorkspaceInputTargets } from "../../structures/inputTargets";
import { WorkspaceRoot } from "../../structures/workspaceRoot";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { updateWorkspaceCache } from "../cacheHandlers/cacheUpdater";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";
import { parseCoqProject } from "../coqProjectParser/parseCoqProject";
import { ParsedWorkspaceHolder } from "../coqProjectParser/parsedWorkspaceHolder";

export async function parseMissingTargetsAndUpdateCache(
    missingTargets: WorkspaceInputTargets,
    workspaceCacheToUpdate: WorkspaceCacheHolder,
    workspaceRoot: WorkspaceRoot,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: AsyncScheduler,
    logger: BenchmarkingLogger
) {
    const parsedWorkspace = await parseCoqProject(
        missingTargets,
        workspaceRoot,
        runOptions,
        subprocessesScheduler,
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
    logger.info(
        `Successfully updated in-memory cache for ${workspaceCache.workspacePath} workspace: ${parsedWorkspace.parsedFilesNumber()} file(s) updated`
    );
}
