import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../../core/coqProofChecker";

import { TimeMark } from "../../../../../benchmark/framework/benchmarkCompletionGeneration/measureUtils";
import { CheckProofsBySubprocessSignature } from "../../../../../benchmark/framework/subprocessCalls/checkGeneratedProofs/callSignature";
import { executeAsFunctionOnParentProcessCall } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { LogsIPCSender } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { subprocessExecutable } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";
import { stringifyAnyValue } from "../../../../../utils/printers";
import { createCoqLspClient } from "../../utils/coqLspUtils";

import Signature = CheckProofsBySubprocessSignature;

subprocessExecutable(Signature.subprocessName, () =>
    executeAsFunctionOnParentProcessCall<Signature.Args, Signature.Result>(
        Signature.argsSchema,
        Signature.resultSchema,
        checkGeneratedProofsMeasured
    )
);

async function checkGeneratedProofsMeasured(
    args: Signature.Args,
    logger: LogsIPCSender
): Promise<Signature.Result> {
    const coqLspClient = createCoqLspClient(args.workspaceRootPath);
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
        return buildSuccessResult(proofCheckResults, proofsValidationMillis);
    } catch (e) {
        const error = e as Error;
        if (error === null) {
            throw Error(
                `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
            );
        }
        // TODO: maybe it will be more efficient just to rethrow error here
        if (error instanceof CoqLspTimeoutError) {
            logger.debug(
                `coq-lsp timeout error: ${stringifyAnyValue(error.message)}`
            );
            return buildFailureResult("TIMEOUT", error.message);
        } else {
            logger.debug(
                `\`CoqProofChecker\` error: ${stringifyAnyValue(error.message)}`
            );
            return buildFailureResult("COQ_PROOF_CHECKER_ERROR", error.message);
        }
    }
}

function buildSuccessResult(
    proofCheckResults: ProofCheckResult[],
    proofsValidationMillis: number
): Signature.SuccessResult {
    return {
        proofCheckResults: proofCheckResults,
        proofsValidationMillis: proofsValidationMillis,
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
