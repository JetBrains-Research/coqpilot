import { stringifyAnyValue } from "../../../utils/printers";
import { ConfigurationError } from "../../llmServiceErrors";
import { UserModelParams } from "../../userModelParams";
import { LLMService } from "../llmService";
import { ModelParams } from "../modelParams";

import { ParamsResolutionResult } from "./paramsResolvers/abstractResolvers";
import { ParamsResolverImpl } from "./paramsResolvers/paramsResolverImpl";

export function resolveOrThrow<InputType, ResolveToType>(
    paramsResolver: ParamsResolverImpl<InputType, ResolveToType>,
    inputParams: InputType
): ResolveToType {
    const resolutionResult = paramsResolver.resolve(inputParams);
    return unpackResolvedParamsOrThrow(resolutionResult, inputParams);
}

export function resolveParametersOrThrow<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    llmService: LLMService<InputModelParams, ResolvedModelParams>,
    inputParams: InputModelParams
): ResolvedModelParams {
    const resolutionResult = llmService.resolveParameters(inputParams);
    return unpackResolvedParamsOrThrow(resolutionResult, inputParams);
}

function unpackResolvedParamsOrThrow<InputType, ResolveToType>(
    resolutionResult: ParamsResolutionResult<ResolveToType>,
    inputParams: InputType
): ResolveToType {
    if (resolutionResult.resolved !== undefined) {
        return resolutionResult.resolved;
    }
    const joinedErrorLogs = resolutionResult.resolutionLogs
        .filter((paramLog) => paramLog.isInvalidCause !== undefined)
        .map((paramLog) => paramLog.isInvalidCause)
        .join("; ");
    throw new ConfigurationError(
        `parameters ${stringifyAnyValue(inputParams)} could not be resolved: ${joinedErrorLogs}`
    );
}
