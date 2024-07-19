import { createTestCoqLspClient } from "../../../../coqLsp/coqLspBuilders";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";
import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../core/coqProofChecker";
import { getTextBeforePosition } from "../../../../core/exposedCompletionGeneratorUtils";

import { TimeMark } from "../../../../benchmark/framework/benchmarkCompletionGeneration/measureUtils";
import { BenchmarkingLogger } from "../../../../benchmark/framework/logging/benchmarkingLogger";
import { stringifyAnyValue } from "../../../../utils/printers";

export namespace ProofsValidation {
    export type Result = SuccessResult | FailureResult;

    export interface SuccessResult {
        proofCheckResults: ProofCheckResult[];
        proofsValidationMillis: number;
    }

    export type FailureType = "TIMEOUT" | "COQ_PROOF_CHECKER_ERROR";

    export interface FailureResult {
        failureType: FailureType;
        causeMessage: string;
    }

    export function isSuccess(result: Result): result is SuccessResult {
        return "proofCheckResults" in result;
    }

    export function isFailure(result: Result): result is FailureResult {
        return "failureType" in result;
    }

    export async function checkGeneratedProofs(
        preparedProofs: string[],
        completionContext: CompletionContext,
        sourceFileEnvironment: SourceFileEnvironment,
        workspaceRootDirectoryPath: string | undefined,
        timeoutMillis: number | undefined,
        logger: BenchmarkingLogger
    ): Promise<Result> {
        const coqLspClient = createTestCoqLspClient(workspaceRootDirectoryPath);
        const coqProofChecker = new CoqProofChecker(coqLspClient);
        // TODO: each coq proof checker should use its own prefix to work good in parallel (many checkers for the same theorem in the same file)
        try {
            const timeMark = new TimeMark();
            const proofCheckResults = await coqProofChecker.checkProofs(
                sourceFileEnvironment.dirPath,
                getTextBeforePosition(
                    sourceFileEnvironment.fileLines,
                    completionContext.prefixEndPosition
                ),
                completionContext.prefixEndPosition,
                preparedProofs,
                timeoutMillis
            );
            const proofsValidationMillis = timeMark.measureElapsedMillis();
            return buildSuccessResult(
                proofCheckResults,
                proofsValidationMillis
            );
        } catch (e) {
            const error = e as Error;
            if (error === null) {
                throw Error(
                    `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
                );
            }
            if (error instanceof CoqLspTimeoutError) {
                logger.debug(
                    `coq-lsp timeout error: ${stringifyAnyValue(error.message)}`
                );
                return buildProofsCheckingFailureResult(
                    "TIMEOUT",
                    error.message
                );
            } else {
                logger.debug(
                    `\`CoqProofChecker\` error: ${stringifyAnyValue(error.message)}`
                );
                return buildProofsCheckingFailureResult(
                    "COQ_PROOF_CHECKER_ERROR",
                    error.message
                );
            }
        }
    }

    function buildSuccessResult(
        proofCheckResults: ProofCheckResult[],
        proofsValidationMillis: number
    ): SuccessResult {
        return {
            proofCheckResults: proofCheckResults,
            proofsValidationMillis: proofsValidationMillis,
        };
    }

    function buildProofsCheckingFailureResult(
        failureType: FailureType,
        causeMessage: string
    ): FailureResult {
        return {
            failureType: failureType,
            causeMessage: causeMessage,
        };
    }
}
