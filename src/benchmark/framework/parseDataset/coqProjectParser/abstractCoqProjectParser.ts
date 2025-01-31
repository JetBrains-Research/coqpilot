import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/common/inputTargets";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";

import { ParsedWorkspaceHolder } from "./implementation/parsedWorkspaceHolder";

export class CoqProjectParsingFailedError extends Error {
    constructor(
        readonly errorTypeName: string,
        message: string
    ) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CoqProjectParsingFailedError";
    }
}

export abstract class AbstractCoqProjectParser {
    abstract parseCoqProject(
        targets: WorkspaceInputTargets,
        workspaceRoot: WorkspaceRoot,
        openDocumentTimeoutMillis: number | undefined,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder>;
}
