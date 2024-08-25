import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/inputTargets";
import { WorkspaceRoot } from "../../structures/workspaceRoot";

import { ParsedWorkspaceHolder } from "./parsedWorkspaceHolder";

export abstract class AbstractCoqProjectParser {
    abstract parseCoqProject(
        targets: WorkspaceInputTargets,
        workspaceRoot: WorkspaceRoot,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder>;
}
