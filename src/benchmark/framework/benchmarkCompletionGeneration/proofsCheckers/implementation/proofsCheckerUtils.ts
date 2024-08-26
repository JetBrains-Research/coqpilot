import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../core/completionGenerationContext";
import { getTextBeforePosition } from "../../../../../core/exposedCompletionGeneratorUtils";

import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../../structures/workspaceRoot";
import {
    ProofsCheckFailedError,
    ProofsCheckResult,
} from "../abstractProofsChecker";

import { CheckProofsInternalSignature } from "./internalSignature";

export namespace ProofsCheckerUtils {
    import Signature = CheckProofsInternalSignature;

    export function buildArgs(
        preparedProofs: string[],
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        workspaceRoot: WorkspaceRoot
    ): Signature.Args {
        return {
            workspaceRootPath: isStandaloneFilesRoot(workspaceRoot)
                ? undefined
                : workspaceRoot.directoryPath,
            sourceFileDirPath: sourceFileEnvironment.dirPath,
            sourceFileContentPrefix: getTextBeforePosition(
                sourceFileEnvironment.fileLines,
                completionContext.prefixEndPosition
            ),
            prefixEndPosition: completionContext.prefixEndPosition,
            preparedProofs: preparedProofs,
        };
    }

    export function unpackSuccessResultOrThrow(
        proofsCheckResult: Signature.Result
    ): ProofsCheckResult {
        if (Signature.isFailure(proofsCheckResult)) {
            throw new ProofsCheckFailedError(
                proofsCheckResult.failureType,
                proofsCheckResult.causeMessage
            );
        }
        return proofsCheckResult as ProofsCheckResult;
    }
}
