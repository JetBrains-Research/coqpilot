import { CheckProofsImpl } from "../../../../../benchmark/framework/benchmarkingCore/singleCompletionGeneration/proofsCheckers/implementation/checkProofs";
import { CheckProofsInternalSignature } from "../../../../../benchmark/framework/benchmarkingCore/singleCompletionGeneration/proofsCheckers/implementation/internalSignature";
import { executeAsFunctionOnParentProcessCall } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { LogsIPCSender } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { subprocessExecutable } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

import Signature = CheckProofsInternalSignature;

subprocessExecutable(Signature.subprocessName, () =>
    executeAsFunctionOnParentProcessCall<Signature.Args, Signature.Result>(
        Signature.argsSchema,
        Signature.resultSchema,
        (args: Signature.Args, logger: LogsIPCSender) =>
            CheckProofsImpl.checkProofsMeasured(args, {
                logger: logger,
                logSuccess: true,
            })
    )
);
