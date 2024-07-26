import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    WorkspaceRoot,
    isNoWorkspaceRoot,
} from "../../structures/completionGenerationTask";
import { ExperimentRunOptions } from "../../structures/experimentRunOptions";
import {
    AllTheoremsTarget,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../../structures/inputTargets";
import { buildAndParseCoqProjectInSubprocess } from "../../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../../subprocessCalls/buildAndParseCoqProject/callSignature";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { entriesToMappedObject } from "../../utils/mapUtils";

import { ParsedWorkspaceHolder } from "./parsedWorkspaceHolder";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

export async function parseCoqProjectForMissingTargets(
    missingTargets: WorkspaceInputTargets,
    workspaceRoot: WorkspaceRoot,
    runOptions: ExperimentRunOptions,
    subprocessesScheduler: AsyncScheduler,
    logger: BenchmarkingLogger
): Promise<ParsedWorkspaceHolder> {
    const executionResult = await buildAndParseCoqProjectInSubprocess(
        workspaceRoot,
        packWorkspaceTargets(missingTargets),
        false, // TODO: support turning projects building on
        runOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
        subprocessesScheduler,
        logger,
        runOptions.enableSubprocessLifetimeDebugLogs
    );
    const projectId = isNoWorkspaceRoot(workspaceRoot)
        ? "standalone source files requested"
        : `"${workspaceRoot.directoryPath}" project with source files requested`;
    if (executionResult.isFailed()) {
        logger
            .asOneRecord()
            .error(`failed to build and parse ${projectId}`, undefined, "")
            .debug(`: ${missingTargets.filePaths().join(", ")}`, undefined, "")
            .error(
                `\n\tcaused by \`${executionResult.errorTypeName}\`: ${executionResult.errorMessage}`
            );
        throw Error("failed to build benchmarking items");
    }
    const parsedWorkspaceHolder = executionResult.maybeResult!;
    logger.info(
        `Successfully parsed ${projectId}: ${parsedWorkspaceHolder.parsedFilesNumber()} files`
    );
    return parsedWorkspaceHolder;
}

function packWorkspaceTargets(
    missingTargets: WorkspaceInputTargets
): Signature.ArgsModels.FilePathToFileTargets {
    const mappedEntries: [string, Signature.ArgsModels.FileTarget[]][] =
        missingTargets.entries().map(([filePath, fileTargets]) => {
            return [
                filePath,
                fileTargets.map((fileTarget) => {
                    if (fileTarget instanceof AllTheoremsTarget) {
                        return {
                            requestType: fileTarget.requestType,
                            specificTheoremName: undefined,
                        };
                    } else if (fileTarget instanceof SpecificTheoremTarget) {
                        return {
                            requestType: fileTarget.requestType,
                            specificTheoremName: fileTarget.theoremName,
                        };
                    } else {
                        throw Error(
                            `Unknown input file target: ${fileTarget.toString("", "")}`
                        );
                    }
                }),
            ];
        });
    return entriesToMappedObject(mappedEntries);
}
