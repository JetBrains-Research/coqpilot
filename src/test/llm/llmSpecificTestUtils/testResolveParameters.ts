import { expect } from "earl";

import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { defaultMultiroundProfile } from "../../../llm/llmServices/utils/paramsResolvers/basicModelParamsResolvers";
import {
    UserModelParams,
    UserMultiroundProfile,
} from "../../../llm/userModelParams";

/**
 * "User" version of `defaultUserMultiroundProfile` having the same default values.
 * This constant is needed because `proofFixChoices` and `defaultProofFixChoices`
 * parameters have different names.
 */
export const defaultUserMultiroundProfile: UserMultiroundProfile = {
    maxRoundsNumber: defaultMultiroundProfile.maxRoundsNumber,
    proofFixChoices: defaultMultiroundProfile.defaultProofFixChoices,
    proofFixPrompt: defaultMultiroundProfile.proofFixPrompt,
};

export function testResolveValidCompleteParameters<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    llmService: LLMService<InputModelParams, ResolvedModelParams>,
    validInputParams: InputModelParams,
    expectNoDefaultResolutions: boolean = false
) {
    const resolutionResult = llmService.resolveParameters(validInputParams);
    expect(resolutionResult.resolved).not.toBeNullish();
    // verify logs
    for (const paramLog of resolutionResult.resolutionLogs) {
        expect(paramLog.resultValue).not.toBeNullish();
        expect(paramLog.isInvalidCause).toBeNullish();
        if (expectNoDefaultResolutions) {
            expect(paramLog.inputReadCorrectly.wasPerformed).toBeTruthy();
            expect(paramLog.resolvedWithDefault.wasPerformed).toBeFalsy();
        }
    }
}

export function testResolveParametersFailsWithSingleCause<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
>(
    llmService: LLMService<InputModelParams, ResolvedModelParams>,
    invalidInputParams: InputModelParams,
    invalidCauseSubstring: string
) {
    const resolutionResult = llmService.resolveParameters(invalidInputParams);
    expect(resolutionResult.resolved).toBeNullish();
    const failureLogs = resolutionResult.resolutionLogs.filter(
        (paramLog) => paramLog.isInvalidCause !== undefined
    );
    expect(failureLogs).toHaveLength(1);
    const invalidCause = failureLogs[0].isInvalidCause;
    expect(invalidCause?.includes(invalidCauseSubstring)).toBeTruthy();
}
