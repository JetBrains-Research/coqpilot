import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import {
    AllTheoremsTarget,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../../structures/inputTargets";
import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../structures/workspaceRoot";
import { buildAndParseCoqProjectInSubprocess } from "../../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../../subprocessCalls/buildAndParseCoqProject/callSignature";
import { AsyncScheduler } from "../../utils/asyncScheduler";
import { entriesToMappedObject } from "../../utils/mapUtils";

import { AbstractCoqProjectParser } from "./abstractCoqProjectParser";
import { ParsedWorkspaceHolder } from "./parsedWorkspaceHolder";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

export class SubprocessCoqProjectParser extends AbstractCoqProjectParser {
    constructor(
        private readonly subprocessesScheduler: AsyncScheduler,
        private readonly buildAndParseCoqProjectSubprocessTimeoutMillis:
            | number
            | undefined,
        private readonly enableSubprocessLifetimeDebugLogs: boolean
    ) {
        super();
    }

    async parseCoqProject(
        targets: WorkspaceInputTargets,
        workspaceRoot: WorkspaceRoot,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder> {
        const executionResult = await buildAndParseCoqProjectInSubprocess(
            workspaceRoot,
            this.packWorkspaceTargets(targets),
            false, // TODO: support turning projects building on
            this.buildAndParseCoqProjectSubprocessTimeoutMillis,
            this.subprocessesScheduler,
            logger,
            this.enableSubprocessLifetimeDebugLogs
        );
        const projectId = isStandaloneFilesRoot(workspaceRoot)
            ? "standalone source files requested"
            : `"${workspaceRoot.directoryPath}" project with source files requested`;
        if (executionResult.isFailed()) {
            logger
                .asOneRecord()
                .error(`failed to build and parse ${projectId}`, undefined, "")
                .debug(`: ${targets.filePaths().join(", ")}`, undefined, "")
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

    private packWorkspaceTargets(
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
                        } else if (
                            fileTarget instanceof SpecificTheoremTarget
                        ) {
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
}
