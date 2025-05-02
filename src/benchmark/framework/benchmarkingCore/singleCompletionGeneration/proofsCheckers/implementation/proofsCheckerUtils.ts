import { serializeUri } from "../../../../structures/common/serializedUri";
import { isStandaloneFilesRoot } from "../../../../structures/common/workspaceRoot";
import {
    ProofsCheckArgs,
    ProofsCheckFailedError,
    ProofsCheckResult,
} from "../abstractProofsChecker";

import { CheckProofsInternalSignature } from "./internalSignature";

export namespace ProofsCheckerUtils {
    import Signature = CheckProofsInternalSignature;

    export function buildArgs(
        preparedProofs: string[],
        inputArgs: ProofsCheckArgs
    ): Signature.Args {
        return {
            workspaceRootPath: isStandaloneFilesRoot(inputArgs.workspaceRoot)
                ? undefined
                : inputArgs.workspaceRoot.directoryPath,
            serializedFileUri: serializeUri(
                inputArgs.sourceFileEnvironment.fileUri
            ),
            documentVersion: inputArgs.sourceFileEnvironment.documentVersion,
            positionToCheckAt: inputArgs.completionContext.admitRange.start,
            preparedProofs: preparedProofs,
            openDocumentTimeoutMillis: inputArgs.openDocumentTimeoutMillis,
            proofCheckTimeoutMillis: inputArgs.proofCheckTimeoutMillis,
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
