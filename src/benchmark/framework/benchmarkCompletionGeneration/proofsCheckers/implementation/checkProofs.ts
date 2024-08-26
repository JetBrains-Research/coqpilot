import { createTestCoqLspClient } from "../../../../../coqLsp/coqLspBuilders";

import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../../core/coqProofChecker";

import { stringifyAnyValue } from "../../../../../utils/printers";
import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { LogsIPCSender } from "../../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { TimeMark } from "../../measureUtils";

import { CheckProofsInternalSignature } from "./internalSignature";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export namespace CheckProofsImpl {
    import Signature = CheckProofsInternalSignature;

    export type Logger = LogsIPCSender | BenchmarkingLogger;

    export async function checkProofsMeasured(
        args: Signature.Args,
        logger: Logger
    ): Promise<Signature.Result> {
        const coqLspClient = createTestCoqLspClient(args.workspaceRootPath);
        const coqProofChecker = new CoqProofChecker(coqLspClient);
        // TODO: each coq proof checker should use its own prefix to work good in parallel (many checkers for the same theorem in the same file)

        try {
            const timeMark = new TimeMark();
            const proofCheckResults = await coqProofChecker.checkProofs(
                args.sourceFileDirPath,
                args.sourceFileContentPrefix,
                args.prefixEndPosition,
                args.preparedProofs
            );
            const proofsValidationMillis = timeMark.measureElapsedMillis();
            return buildSuccessResult(
                proofCheckResults,
                proofsValidationMillis,
                logger
            );
        } catch (e) {
            const error = e as Error;
            if (error === null) {
                throw Error(
                    `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
                );
            }
            // TODO: maybe it will be more efficient just to rethrow error here
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
        logger: Logger
    ): Signature.SuccessResult {
        logger.info(
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
