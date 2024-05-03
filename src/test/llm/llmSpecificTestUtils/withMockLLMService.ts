import { EventLogger } from "../../../logging/eventLogger";

import { proofsToGenerate } from "./constants";
import { MockLLMModelParams, MockLLMService } from "./mockLLMService";

export async function withMockLLMService(
    block: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams,
        testEventLogger: EventLogger
    ) => Promise<void>
) {
    const testEventLogger = new EventLogger();
    const mockService = new MockLLMService(testEventLogger, true);
    try {
        const basicMockParams: MockLLMModelParams = {
            modelName: "mock model",
            systemPrompt: MockLLMService.systemPromptToOverrideWith,
            newMessageMaxTokens: 100,
            tokensLimit: 1000,
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 0,
                proofFixPrompt: "Fix proof",
            },
            proofsToGenerate: proofsToGenerate,
            workerId: 0,
            resolvedWithMockLLMService: true,
        };
        await block(mockService, basicMockParams, testEventLogger);
    } finally {
        mockService.dispose();
    }
}
