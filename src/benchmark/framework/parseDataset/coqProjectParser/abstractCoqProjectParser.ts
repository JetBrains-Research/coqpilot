import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/inputTargets";
import { WorkspaceRoot } from "../../structures/workspaceRoot";

import { ParsedWorkspaceHolder } from "./implementation/parsedWorkspaceHolder";

export class CoqProjectParsingFailedError extends Error {
    constructor(
        readonly errorTypeName: string,
        message: string
    ) {
        super(message);
    }
}

export abstract class AbstractCoqProjectParser {
    abstract parseCoqProject(
        targets: WorkspaceInputTargets,
        workspaceRoot: WorkspaceRoot,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder>;
}
