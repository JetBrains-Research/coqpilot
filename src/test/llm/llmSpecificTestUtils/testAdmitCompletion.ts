import { expect } from "earl";

import {
    ErrorsHandlingMode,
    LLMService,
} from "../../../llm/llmServices/llmService";
import { UserModelParams } from "../../../llm/userModelParams";

import { checkTheoremProven } from "../../commonTestFunctions/checkProofs";
import { prepareEnvironmentWithContexts } from "../../commonTestFunctions/prepareEnvironment";
import { withLLMServiceAndParams } from "../../commonTestFunctions/withLLMService";

export async function testLLMServiceCompletesAdmitFromFile(
    service: LLMService,
    userParams: UserModelParams,
    resourcePath: string[],
    choices: number
) {
    await withLLMServiceAndParams(
        service,
        userParams,
        async (service, params) => {
            const [environment, [[completionContext, proofGenerationContext]]] =
                await prepareEnvironmentWithContexts(resourcePath);
            const generatedProofs = await service.generateProof(
                proofGenerationContext,
                params,
                choices,
                ErrorsHandlingMode.RETHROW_ERRORS
            );
            expect(generatedProofs).toHaveLength(choices);
            expect(
                checkTheoremProven(
                    generatedProofs,
                    completionContext,
                    environment
                )
            ).toBeTruthy();
        }
    );
}
