import { asErrorOrRethrow } from "../../../../utils/errorsUtils";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { WorkspaceInputTargets } from "../../structures/common/inputTargets";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";

import {
    AbstractCoqProjectParser,
    CoqProjectParsingFailedError,
} from "./abstractCoqProjectParser";
import { CoqProjectParserUtils } from "./implementation/coqProjectParserUtils";
import { ParseCoqProjectInternalSignature } from "./implementation/internalSignature";
import { ParseCoqProjectImpl } from "./implementation/parseCoqProject";
import { ParsedWorkspaceHolder } from "./implementation/parsedWorkspaceHolder";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export class LocalCoqProjectParser extends AbstractCoqProjectParser {
    async parseCoqProject(
        targets: WorkspaceInputTargets,
        workspaceRoot: WorkspaceRoot,
        logger: BenchmarkingLogger
    ): Promise<ParsedWorkspaceHolder> {
        const workspaceTargets =
            CoqProjectParserUtils.packWorkspaceTargets(targets);
        const args = CoqProjectParserUtils.buildArgs(
            workspaceTargets,
            workspaceRoot
        );
        const parsedWorkspace = await this.parseCoqProjectAndWrapError(
            args,
            logger
        );
        return new ParsedWorkspaceHolder(parsedWorkspace);
    }

    private async parseCoqProjectAndWrapError(
        args: ParseCoqProjectInternalSignature.ArgsModels.Args,
        logger: BenchmarkingLogger
    ) {
        try {
            return await ParseCoqProjectImpl.parseCoqProject(args, logger);
        } catch (e) {
            const error = asErrorOrRethrow(e);
            throw new CoqProjectParsingFailedError(error.name, error.message);
        }
    }
}
