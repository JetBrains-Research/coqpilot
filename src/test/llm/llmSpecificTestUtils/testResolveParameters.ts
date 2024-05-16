import { expect } from "earl";

import { LLMService } from "../../../llm/llmServices/llmService";
import { ModelParams } from "../../../llm/llmServices/modelParams";
import { UserModelParams } from "../../../llm/userModelParams";

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
