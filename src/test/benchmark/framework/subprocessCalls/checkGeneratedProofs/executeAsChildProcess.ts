import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../../core/coqProofChecker";

import { stringifyAnyValue } from "../../../../../utils/printers";
import { TimeMark } from "../../benchmarkCompletionGeneration/measureUtils";
import { createCoqLspClient } from "../../utils/coqLspUtils";
import {
    LogsIPCSender,
    executeAsFunctionOnParentProcessCall,
} from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { subprocessExecutable } from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

import { CheckProofsBySubprocessSignature } from "./callSignature";

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
            return buildFailureResult("timeout", error.message);
        } else {
            logger.debug(
                `\`CoqProofChecker\` error: ${stringifyAnyValue(error.message)}`
            );
            return buildFailureResult("coq-proof-checker-error", error.message);
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
