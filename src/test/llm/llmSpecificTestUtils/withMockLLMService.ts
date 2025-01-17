import { ErrorsHandlingMode } from "../../../llm/llmServices/commonStructures/errorsHandlingMode";

import { EventLogger } from "../../../logging/eventLogger";
import { withLLMService } from "../../commonTestFunctions/withLLMService";

import { proofsToGenerate, testModelId } from "./constants";
import { MockLLMModelParams, MockLLMService } from "./mockLLMService";

export async function withMockLLMService(
    errorsHandlingMode: ErrorsHandlingMode,
    block: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams,
        testEventLogger: EventLogger
    ) => Promise<void>
) {
    const testEventLogger = new EventLogger();
    return withLLMService(
        new MockLLMService(testEventLogger, errorsHandlingMode),
        async (mockService) => {
            const basicMockParams: MockLLMModelParams = {
                modelId: testModelId,
                systemPrompt: MockLLMService.systemPromptToOverrideWith,
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
                multiroundProfile: {
                    maxRoundsNumber: 1,
                    defaultProofFixChoices: 0,
                    proofFixPrompt: "Fix proof",
                },
                defaultChoices: proofsToGenerate.length,
                proofsToGenerate: proofsToGenerate,
                workerId: 0,
                resolvedWithMockLLMService: true,
            };
            await block(mockService, basicMockParams, testEventLogger);
        }
    );
}
