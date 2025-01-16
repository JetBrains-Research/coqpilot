import { withDocumentOpenedByTestCoqLsp } from "../../../../../../coqLsp/coqLspBuilders";
import { CoqLspTimeoutError } from "../../../../../../coqLsp/coqLspTypes";

import {
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../../../core/coqProofChecker";

import {
    asErrorOrRethrowWrapped,
    getErrorMessage,
} from "../../../../../../utils/errorsUtils";
import { deserializeUri } from "../../../../structures/common/serializedUri";
import { FailFastAbortError } from "../../../../utils/asyncUtils/abortUtils";
import { LogsIPCSender } from "../../../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { TimeMark } from "../../measureTimeUtils";

import { CheckProofsInternalSignature } from "./internalSignature";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export namespace CheckProofsImpl {
    import Signature = CheckProofsInternalSignature;

    export type ProvidedLogger = LogsIPCSender | undefined;

    export async function checkProofsMeasured(
        args: Signature.Args,
        providedLogger: ProvidedLogger,
        abortSignal?: AbortSignal
    ): Promise<Signature.Result> {
        const fileUri = deserializeUri(args.serializedFileUri);
        const timeMark = new TimeMark();

        try {
            const proofCheckResults = await withDocumentOpenedByTestCoqLsp(
                { uri: fileUri, version: args.documentVersion },
                {
                    workspaceRootPath: args.workspaceRootPath,
                    abortSignal: abortSignal,
                },
                (coqLspClient) =>
                    new CoqProofChecker(coqLspClient).checkProofs(
                        fileUri,
                        args.documentVersion,
                        args.positionToCheckAt,
                        args.preparedProofs
                    )
            );
            const proofsValidationMillis = timeMark.measureElapsedMillis();

            return buildSuccessResult(
                proofCheckResults,
                proofsValidationMillis,
                providedLogger
            );
        } catch (e) {
            const error = asErrorOrRethrowWrapped(
                e,
                "got unexpected error from `CoqProofChecker`"
            );
            // TODO: just rethrow error here, packing-unpacking should be carefully removed
            if (error instanceof FailFastAbortError) {
                throw error;
            } else if (error instanceof CoqLspTimeoutError) {
                providedLogger?.error(
                    `\`coq-lsp\` timeout error: ${getErrorMessage(error)}`
                );
                return buildFailureResult("COQ_LSP_TIMEOUT", error.message);
            } else {
                providedLogger?.error(
                    `\`CoqProofChecker\` error: ${getErrorMessage(error)}`
                );
                return buildFailureResult(
                    "COQ_PROOF_CHECKER_ERROR",
                    error.message
                );
            }
        }
    }

    function buildSuccessResult(
        proofCheckResults: ProofCheckResult[],
        proofsValidationMillis: number,
        providedLogger: ProvidedLogger
    ): Signature.SuccessResult {
        providedLogger?.debug(
            `Proofs were successfully checked in ${proofsValidationMillis} ms`
        );
        return {
            checkedProofs: proofCheckResults,
            effectiveElapsedMillis: proofsValidationMillis,
        };
    }

    function buildFailureResult(
        failureType: Signature.FailureType,
        causeMessage: string
    ): Signature.FailureResult {
        return {
            failureType: failureType,
            causeMessage: causeMessage,
        };
    }
}
