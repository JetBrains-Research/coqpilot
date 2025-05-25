import { ErrorsHandlingMode } from "../../../proofProviders/impl/commonStructures/errorsHandlingMode";

import { EventLogger } from "../../../logging/eventLogger";
import { withProofProvider } from "../../commonTestFunctions/withProofProvider";

import { proofsToGenerate, testModelId } from "./constants";
import { MockService, MockServiceModelParams } from "./mockService";

export async function withMockService(
    errorsHandlingMode: ErrorsHandlingMode,
    block: (
        mockService: MockService,
        basicMockParams: MockServiceModelParams,
        testEventLogger: EventLogger
    ) => Promise<void>
) {
    const testEventLogger = new EventLogger();
    return withProofProvider(
        new MockService(testEventLogger, errorsHandlingMode),
        async (mockService) => {
            const basicMockParams: MockServiceModelParams = {
                modelId: testModelId,
                systemPrompt: MockService.systemPromptToOverrideWith,
                maxTokensToGenerate: 100,
                tokensLimit: 1000,
                maxContextTheoremsNumber: Number.MAX_SAFE_INTEGER,
                multiroundProfile: {
                    maxRoundsNumber: 1,
                    defaultProofFixChoices: 0,
                    proofFixPrompt: "Fix proof",
                    maxPreviousProofVersionsNumber: Number.MAX_SAFE_INTEGER,
                },
                defaultChoices: proofsToGenerate.length,
                proofsToGenerate: proofsToGenerate,
                workerId: 0,
                resolvedWithMockService: true,
            };
            await block(mockService, basicMockParams, testEventLogger);
        }
    );
}
