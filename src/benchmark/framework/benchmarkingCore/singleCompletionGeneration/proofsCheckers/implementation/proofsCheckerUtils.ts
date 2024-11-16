import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../../../core/completionGenerationContext";

import { serializeUri } from "../../../../structures/common/serializedUri";
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
            serializedFileUri: serializeUri(sourceFileEnvironment.fileUri),
            documentVersion: sourceFileEnvironment.documentVersion,
            positionToCheckAt: completionContext.admitRange.start,
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
