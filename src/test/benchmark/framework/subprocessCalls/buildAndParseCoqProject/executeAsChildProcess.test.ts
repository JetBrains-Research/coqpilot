import { ParseCoqProjectInternalSignature } from "../../../../../benchmark/framework/parseDataset/coqProjectParser/implementation/internalSignature";
import { ParseCoqProjectImpl } from "../../../../../benchmark/framework/parseDataset/coqProjectParser/implementation/parseCoqProject";
import { executeAsFunctionOnParentProcessCall } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { subprocessExecutable } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

import Signature = ParseCoqProjectInternalSignature;

subprocessExecutable(Signature.subprocessName, () =>
    executeAsFunctionOnParentProcessCall<
        Signature.ArgsModels.Args,
        Signature.ResultModels.Result
    >(
        Signature.ArgsModels.argsSchema,
        Signature.ResultModels.resultSchema,
        ParseCoqProjectImpl.parseCoqProject
    )
);
