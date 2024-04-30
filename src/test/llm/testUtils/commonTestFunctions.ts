import { expect } from "earl";
import { TiktokenModel, encoding_for_model } from "tiktoken";

import {
    ErrorsHandlingMode,
    LLMService,
} from "../../../llm/llmServices/llmService";
import { UserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import {
    checkTheoremProven,
    prepareEnvironmentWithContexts,
} from "../../commonTestFunctions";

export const gptTurboModel = "gpt-3.5-turbo-0301";

export function calculateTokensViaTikToken(
    text: string,
    model: TiktokenModel
): number {
    const encoder = encoding_for_model(model);
    const tokens = encoder.encode(text).length;
    encoder.free();
    return tokens;
}

export function approxCalculateTokens(text: string): number {
    return (text.length / 4) >> 0;
}

export interface EventsTracker {
    successfulGenerationEventsN: number;
    failedGenerationEventsN: number;
}

export function subscribeToTrackEvents(
    testEventLogger: EventLogger,
    targetService: LLMService
): EventsTracker {
    const eventsTracker: EventsTracker = {
        successfulGenerationEventsN: 0,
        failedGenerationEventsN: 0,
    };
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationSucceededEvent,
        (service) => {
            expect(service).toEqual(targetService);
            eventsTracker.successfulGenerationEventsN += 1;
        }
    );
    testEventLogger.subscribeToLogicEvent(
        LLMService.generationFailedEvent,
        (service) => {
            expect(service).toEqual(targetService);
            eventsTracker.failedGenerationEventsN += 1;
        }
    );
    return eventsTracker;
}

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
