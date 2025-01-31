import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/common/inputTargets";
import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../structures/common/workspaceRoot";
import { ExperimentRunOptions } from "../../structures/inputParameters/experimentRunOptions";
import { throwBenchmarkingError } from "../../utils/throwErrors";
import { updateWorkspaceCache } from "../cacheHandlers/cacheUpdater";
import { WorkspaceCacheHolder } from "../cacheStructures/cacheHolders";
import {
    AbstractCoqProjectParser,
    CoqProjectParsingFailedError,
} from "../coqProjectParser/abstractCoqProjectParser";
import { ParsedWorkspaceHolder } from "../coqProjectParser/implementation/parsedWorkspaceHolder";

export async function parseMissingTargetsAndUpdateCache(
    missingTargets: WorkspaceInputTargets,
    workspaceCacheToUpdate: WorkspaceCacheHolder,
    workspaceRoot: WorkspaceRoot,
    runOptions: ExperimentRunOptions, // TODO: extract dataset-parsing options into separate interface
    logger: BenchmarkingLogger,
    parser: AbstractCoqProjectParser
) {
    const parsedWorkspace = await parseCoqProject(
        missingTargets,
        workspaceRoot,
        runOptions.openDocumentTimeoutMillis,
        logger,
        parser
    );
    updateCacheWithParsedTargets(
        workspaceCacheToUpdate,
        parsedWorkspace,
        logger
    );
}

async function parseCoqProject(
    missingTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    openDocumentTimeoutMillis: number | undefined,
    logger: BenchmarkingLogger,
    parser: AbstractCoqProjectParser
): Promise<ParsedWorkspaceHolder> {
    const projectId = isStandaloneFilesRoot(workspaceRoot)
        ? "standalone source files requested"
        : `"${workspaceRoot.directoryPath}" project with source files requested`;
    try {
        const parsedWorkspace = await parser.parseCoqProject(
            missingTargets,
            workspaceRoot,
            openDocumentTimeoutMillis,
            logger
        );
        logger.info(
            `Successfully parsed ${projectId}: ${parsedWorkspace.parsedFilesNumber()} files`
        );
        return parsedWorkspace;
    } catch (error) {
        const errorRecordLogger = logger
            .asOneRecord()
            .error(`Failed to build and parse ${projectId}`, undefined, "")
            .debug(`: ${missingTargets.filePaths().join(", ")}`, undefined, "");
        if (error instanceof CoqProjectParsingFailedError) {
            errorRecordLogger.error(
                `\n\tcaused by \`${error.errorTypeName}\`: ${error.message}`
            );
        } else {
            errorRecordLogger.error(
                `\n\tcaused by an unexpected error: ${stringifyAnyValue(error)}`
            );
        }
        throwBenchmarkingError("failed to build benchmarking items");
    }
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
