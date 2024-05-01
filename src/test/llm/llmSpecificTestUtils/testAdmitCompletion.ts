import { expect } from "earl";

import {
    ErrorsHandlingMode,
    LLMService,
} from "../../../llm/llmServices/llmService";
import { UserModelParams } from "../../../llm/userModelParams";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import { prepareEnvironmentWithContexts } from "../../commonTestFunctions/prepareEnvironment";

export async function testLLMServiceCompletesAdmitFromFile(
    service: LLMService,
    userParams: UserModelParams,
    resourcePath: string[],
    choices: number
) {
    const params = service.resolveParameters(userParams);
    const [environment, [[completionContext, proofGenerationContext]]] =
        await prepareEnvironmentWithContexts(resourcePath);
    try {
        const generatedProofs = await service.generateProof(
            proofGenerationContext,
            params,
            choices,
            ErrorsHandlingMode.RETHROW_ERRORS
        );
        expect(generatedProofs).toHaveLength(choices);
        expect(
            checkTheoremProven(generatedProofs, completionContext, environment)
        ).toBeTruthy();
    } finally {
        service.dispose();
    }
}
