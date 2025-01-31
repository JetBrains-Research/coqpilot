import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/common/inputTargets";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { buildAndParseCoqProjectInSubprocess } from "../../subprocessCalls/buildAndParseCoqProject/callChildProcess";
import { AsyncScheduler } from "../../utils/asyncUtils/asyncScheduler";

import {
    AbstractCoqProjectParser,
    CoqProjectParsingFailedError,
} from "./abstractCoqProjectParser";
import { CoqProjectParserUtils } from "./implementation/coqProjectParserUtils";
import { ParsedWorkspaceHolder } from "./implementation/parsedWorkspaceHolder";

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
        openDocumentTimeoutMillis: number | undefined,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder> {
        const executionResult = await buildAndParseCoqProjectInSubprocess(
            workspaceRoot,
            CoqProjectParserUtils.packWorkspaceTargets(targets),
            openDocumentTimeoutMillis,
            false, // TODO: support turning projects building on
            this.buildAndParseCoqProjectSubprocessTimeoutMillis,
            this.subprocessesScheduler,
            logger,
            this.enableSubprocessLifetimeDebugLogs
        );
        if (executionResult.isFailed()) {
            throw new CoqProjectParsingFailedError(
                executionResult.errorTypeName ?? "<undefined error type>",
                executionResult.errorMessage
            );
        } else {
            return executionResult.maybeResult!;
        }
    }
}
