import { EventLogger } from "../../../logging/eventLogger";
import { withLLMService } from "../../commonTestFunctions/withLLMService";

import { proofsToGenerate, testModelId } from "./constants";
import { MockLLMModelParams, MockLLMService } from "./mockLLMService";

export async function withMockLLMService(
    block: (
        mockService: MockLLMService,
        basicMockParams: MockLLMModelParams,
        testEventLogger: EventLogger
    ) => Promise<void>
) {
    const testEventLogger = new EventLogger();
    return withLLMService(
        new MockLLMService(testEventLogger, true),
        async (mockService) => {
            const basicMockParams: MockLLMModelParams = {
                modelId: testModelId,
                systemPrompt: MockLLMService.systemPromptToOverrideWith,
                maxTokensToGenerate: 100,
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
        }
    );
}
