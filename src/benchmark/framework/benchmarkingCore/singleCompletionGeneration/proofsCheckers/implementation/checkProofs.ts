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
        const totalTimeMark = new TimeMark();

        try {
            const [proofCheckResults, proofCheckMillis] =
                await withDocumentOpenedByTestCoqLsp<
                    [ProofCheckResult[], number]
                >(
                    { uri: fileUri, version: args.documentVersion },
                    {
                        workspaceRootPath: args.workspaceRootPath,
                        abortSignal: abortSignal,
                    },
                    async (coqLspClient) => {
                        const proofCheckTimeMark = new TimeMark();
                        const proofCheckResults = await new CoqProofChecker(
                            coqLspClient
                        ).checkProofs(
                            fileUri,
                            args.documentVersion,
                            args.positionToCheckAt,
                            args.preparedProofs,
                            args.proofCheckTimeoutMillis
                        );
                        return [
                            proofCheckResults,
                            proofCheckTimeMark.measureElapsedMillis(),
                        ];
                    }
                );
            const totalMillis = totalTimeMark.measureElapsedMillis();

            return buildSuccessResult(
                proofCheckResults,
                proofCheckMillis,
                totalMillis,
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
        proofCheckMillis: number,
        totalMillis: number,
        providedLogger: ProvidedLogger
    ): Signature.SuccessResult {
        providedLogger?.debug(
            `Proofs were successfully checked in ${totalMillis} ms`
        );
        return {
            checkedProofs: proofCheckResults,
            proofCheckElapsedMillis: proofCheckMillis,
            totalEffectiveElapsedMillis: totalMillis,
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
