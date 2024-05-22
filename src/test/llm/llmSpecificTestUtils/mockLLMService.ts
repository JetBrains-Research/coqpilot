import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

import { ConfigurationError } from "../../../llm/llmServiceErrors";
import {
    AnalyzedChatHistory,
    ChatHistory,
    ChatMessage,
} from "../../../llm/llmServices/chat";
import {
    ErrorsHandlingMode,
    GeneratedProofImpl,
    LLMServiceImpl,
    ProofVersion,
} from "../../../llm/llmServices/llmService";
import { LLMServiceInternal } from "../../../llm/llmServices/llmServiceInternal";
import {
    ModelParams,
    modelParamsSchema,
} from "../../../llm/llmServices/modelParams";
import { BasicModelParamsResolver } from "../../../llm/llmServices/utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../../../llm/llmServices/utils/paramsResolvers/builders";
import { ValidParamsResolverImpl } from "../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { ProofGenerationContext } from "../../../llm/proofGenerationContext";
import { UserModelParams } from "../../../llm/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";

export interface MockLLMUserModelParams extends UserModelParams {
    proofsToGenerate: string[];
    workerId?: number;
}

export interface MockLLMModelParams extends ModelParams {
    proofsToGenerate: string[];
    workerId: number;
    resolvedWithMockLLMService: boolean;
}

export const mockLLMModelParamsSchema: JSONSchemaType<MockLLMModelParams> = {
    title: "MockLLMModelsParameters",
    type: "object",
    properties: {
        proofsToGenerate: {
            type: "array",
            items: { type: "string" },
        },
        workerId: { type: "number" },
        resolvedWithMockLLMService: { type: "boolean" },
        ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
    },
    required: [
        "proofsToGenerate",
        "workerId",
        "resolvedWithMockLLMService",
        ...modelParamsSchema.required,
    ],
    additionalProperties: false,
};

/**
 * `MockLLMService` parameters resolution does 4 changes to `inputParams`:
 * - resolves undefined `workerId` to 0;
 * - adds extra `resolvedWithMockLLMService: true` property;
 * - overrides original `systemPrompt` with `this.systemPromptToOverrideWith`;
 * - overrides original `choices` to `defaultChoices` with `proofsToGenerate.length`.
 */
export class MockLLMModelParamsResolver
    extends BasicModelParamsResolver<MockLLMUserModelParams, MockLLMModelParams>
    implements
        ValidParamsResolverImpl<MockLLMUserModelParams, MockLLMModelParams>
{
    constructor() {
        super(mockLLMModelParamsSchema, "MockLLMModelParams");
    }

    readonly proofsToGenerate = this.resolveParam<string[]>("proofsToGenerate")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be non-empty"]);

    readonly workerId = this.resolveParam<number>("workerId")
        .default(() => 0)
        .validate([(value) => value >= 0, "be non-negative"]);

    readonly resolvedWithMockLLMService = this.insertParam<boolean>(
        () => true
    ).validate([(value) => value, "be true"]);

    readonly systemPrompt = this.resolveParam<string>("systemPrompt")
        .override(() => MockLLMService.systemPromptToOverrideWith)
        .requiredToBeConfigured()
        .noValidationNeeded();

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override((inputParams) => inputParams.proofsToGenerate.length)
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}

/**
 * This class implements `LLMService` the same way as most of the services do,
 * so as to reuse the default implementations as much as possible.
 *
 * However, to make tests cover more corner cases, `MockLLMService` provides additional features.
 * Check the documentation of its methods below.
 */
export class MockLLMService extends LLMServiceImpl<
    MockLLMUserModelParams,
    MockLLMModelParams,
    MockLLMService,
    MockLLMGeneratedProof,
    MockLLMServiceInternal
> {
    protected readonly internal: MockLLMServiceInternal;
    protected readonly modelParamsResolver = new MockLLMModelParamsResolver();

    constructor(
        eventLogger?: EventLogger,
        debugLogs: boolean = false,
        generationsLogsFilePath?: string
    ) {
        super(
            "MockLLMService",
            eventLogger,
            debugLogs,
            generationsLogsFilePath
        );
        this.internal = new MockLLMServiceInternal(
            this,
            this.eventLoggerGetter,
            this.generationsLoggerBuilder
        );
    }

    static readonly generationFromChatEvent = "mockllm-generation-from-chat";

    static readonly systemPromptToOverrideWith =
        "unique mock-llm system prompt";

    static readonly proofFixPrompt = "Generate `Fixed.` instead of proof.";
    static readonly fixedProofString = "Fixed.";

    /**
     * Use this method to make 1 next generation (for the specified worker) throw the specified error.
     * Workers are meant to be any external entities that would like to separate their behaviour.
     */
    throwErrorOnNextGeneration(error: Error, workerId: number = 0) {
        this.internal.throwErrorOnNextGenerationMap.set(workerId, error);
    }

    /**
     * Adds special control message to the chat, so it would make `MockLLMService`
     * skip first `skipFirstNProofs` proofs at the generation stage.
     */
    transformChatToSkipFirstNProofs(
        baseChat: ChatHistory,
        skipFirstNProofs: number
    ): ChatHistory {
        const controlMessage: ChatMessage = {
            role: "user",
            content: `SKIP_FIRST_PROOFS: ${skipFirstNProofs}`,
        };
        return [...baseChat, controlMessage];
    }

    clearGenerationLogs() {
        this.internal.generationsLogger.resetLogs();
    }
}

export class MockLLMGeneratedProof extends GeneratedProofImpl<
    MockLLMModelParams,
    MockLLMService,
    MockLLMGeneratedProof,
    MockLLMServiceInternal
> {
    constructor(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockLLMModelParams,
        llmServiceInternal: MockLLMServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            proof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal,
            previousProofVersions
        );
    }

    /**
     * Mocks the procces of the implementation of a new regeneration method.
     * Namely, checks whether it is possible.
     */
    nextVersionCanBeGenerated(): Boolean {
        return super.nextVersionCanBeGenerated();
    }

    /**
     * Mocks the process of the implementation of a new regeneration method.
     * Namely, performs the generation using `LLMServiceInternal.generateFromChatWrapped`.
     */
    async generateNextVersion(
        analyzedChat: AnalyzedChatHistory,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<MockLLMGeneratedProof[]> {
        return this.llmServiceInternal.generateFromChatWrapped(
            this.modelParams,
            choices,
            errorsHandlingMode,
            () => {
                if (!this.nextVersionCanBeGenerated()) {
                    throw new ConfigurationError(
                        `next version could not be generated: version ${this.versionNumber()} >= max rounds number ${this.maxRoundsNumber}`
                    );
                }
                return analyzedChat;
            },
            (proof: string) =>
                this.llmServiceInternal.constructGeneratedProof(
                    proof,
                    this.proofGenerationContext,
                    this.modelParams,
                    this.proofVersions
                )
        );
    }
}

class MockLLMServiceInternal extends LLMServiceInternal<
    MockLLMModelParams,
    MockLLMService,
    MockLLMGeneratedProof,
    MockLLMServiceInternal
> {
    throwErrorOnNextGenerationMap: Map<number, Error | undefined> = new Map();

    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockLLMModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): MockLLMGeneratedProof {
        return new MockLLMGeneratedProof(
            proof,
            proofGenerationContext,
            modelParams as MockLLMModelParams,
            this,
            previousProofVersions
        );
    }

    /**
     * Generally, `generateFromChatImpl` simply returns first `choices` proofs from the `MockLLMModelParams.proofsToGenerate`.
     * Each `generateFromChatImpl` call sends logic `this.generationFromChatEvent` event to the `eventLogger`.
     * Special behaviour:
     * - If `throwErrorOnNextGenereation` was registered for `MockLLMModelParams.workerId`,
     *   `generateFromChatImpl` throws this error and then resets this behaviour for the next call.
     * - If `chat` contains special control message (see `transformChatToSkipFirstNProofs`),
     *   several proofs from the beggining of `MockLLMModelParams.proofsToGenerate` will be skipped.
     *   Practically, it provides a way to generate different proofs depending on the `chat` (while `modelParams` stay the same).
     * - If `chat` contains `this.proofFixPrompt` in any of its messages,
     *   then all the generated proofs will be equal to `this.fixedProofString`.
     */
    async generateFromChatImpl(
        chat: ChatHistory,
        params: MockLLMModelParams,
        choices: number
    ): Promise<string[]> {
        this.eventLogger?.logLogicEvent(
            MockLLMService.generationFromChatEvent,
            chat
        );

        const throwError = this.throwErrorOnNextGenerationMap.get(
            params.workerId
        );
        if (throwError !== undefined) {
            try {
                throw throwError;
            } finally {
                this.throwErrorOnNextGenerationMap.set(
                    params.workerId,
                    undefined
                );
            }
        }

        const proofFixPromptInChat = chat.find(
            (message) => message.content === MockLLMService.proofFixPrompt
        );
        if (proofFixPromptInChat !== undefined) {
            return Array(choices).fill(MockLLMService.fixedProofString);
        }

        const lastChatMessage = chat[chat.length - 1];
        const skipFirstNProofsParsed =
            this.parseSkipFirstNProofsIfMatches(lastChatMessage);
        const skipFirstNProofs =
            skipFirstNProofsParsed !== undefined ? skipFirstNProofsParsed : 0;

        const proofsLength = params.proofsToGenerate.length - skipFirstNProofs;
        if (choices > proofsLength) {
            throw Error(
                `\`choices = ${choices}\` > \`available proofs length = ${proofsLength}\``
            );
        }

        return params.proofsToGenerate.slice(
            skipFirstNProofs,
            skipFirstNProofs + choices
        );
    }

    private readonly skipFirstNProofsContentPattern =
        /^SKIP_FIRST_PROOFS: (.*)$/;

    private parseSkipFirstNProofsIfMatches(
        message: ChatMessage
    ): number | undefined {
        const match = message.content.match(
            this.skipFirstNProofsContentPattern
        );
        if (!match) {
            return undefined;
        }
        return parseInt(match[1]);
    }
}
