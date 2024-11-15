import { withDocumentOpenedByTestCoqLsp } from "../../../../../../coqLsp/coqLspBuilders";
import { CoqLspTimeoutError } from "../../../../../../coqLsp/coqLspTypes";

import {
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../../../core/coqProofChecker";

import { stringifyAnyValue } from "../../../../../../utils/printers";
import { Uri } from "../../../../../../utils/uri";
import { BenchmarkingLogger } from "../../../../logging/benchmarkingLogger";
import { LogsIPCSender } from "../../../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { TimeMark } from "../../measureUtils";

import { CheckProofsInternalSignature } from "./internalSignature";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export namespace CheckProofsImpl {
    import Signature = CheckProofsInternalSignature;

    export interface ProvidedLogger {
        logger: LogsIPCSender | BenchmarkingLogger;
        logSuccess: boolean;
    }

    export async function checkProofsMeasured(
        args: Signature.Args,
        providedLogger: ProvidedLogger
    ): Promise<Signature.Result> {
        const fileUri = Uri.fromPath(args.fileUri);
        const timeMark = new TimeMark();

        try {
            const proofCheckResults = await withDocumentOpenedByTestCoqLsp(
                { uri: fileUri, version: args.documentVersion },
                args.workspaceRootPath,
                (coqLspClient) =>
                    new CoqProofChecker(coqLspClient).checkProofs(
                        fileUri,
                        args.documentVersion,
                        args.checkAtPosition,
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
            const error = e as Error;
            if (error === null) {
                throw Error(
                    `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
                );
            }
            // TODO: maybe it will be more efficient just to rethrow error here
            const logger = providedLogger.logger;
            if (error instanceof CoqLspTimeoutError) {
                logger.error(
                    `coq-lsp timeout error: ${stringifyAnyValue(error.message)}`
                );
                return buildFailureResult("TIMEOUT", error.message);
            } else {
                logger.error(
                    `\`CoqProofChecker\` error: ${stringifyAnyValue(error.message)}`
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
        if (providedLogger.logSuccess) {
            providedLogger.logger.debug(
                `Proofs were successfully checked in ${proofsValidationMillis} ms`
            );
        }
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
