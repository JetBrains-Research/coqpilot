import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../../core/completionGenerationContext";

import {
    WorkspaceRoot,
    isStandaloneFilesRoot,
} from "../../../../structures/common/workspaceRoot";
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
            fileUri: sourceFileEnvironment.fileUri.toString(),
            documentVersion: sourceFileEnvironment.fileVersion,
            checkAtPosition: completionContext.admitRange.start,
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
