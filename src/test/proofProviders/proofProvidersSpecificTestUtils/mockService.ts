import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

import {
    AnalyzedChatHistory,
    ChatHistory,
    ChatMessage,
} from "../../../proofProviders/impl/commonStructures/chat";
import { ErrorsHandlingMode } from "../../../proofProviders/impl/commonStructures/errorsHandlingMode";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../../../proofProviders/impl/commonStructures/generatedRawContent";
import { ProofGenerationMetadataHolder } from "../../../proofProviders/impl/commonStructures/proofGenerationMetadata";
import { ProofVersion } from "../../../proofProviders/impl/commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../../../proofProviders/impl/commonStructures/schedulersProviders";
import { GeneratedProof } from "../../../proofProviders/impl/generatedProof";
import {
    ModelParams,
    modelParamsSchema,
} from "../../../proofProviders/impl/modelParams";
import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderInternal } from "../../../proofProviders/impl/proofProviderInternal";
import { ValidationRules } from "../../../proofProviders/impl/utils/paramsResolvers/builders";
import { BasicModelParamsResolver } from "../../../proofProviders/impl/utils/paramsResolvers/kit/basicModelParamsResolvers";
import { ValidParamsResolverImpl } from "../../../proofProviders/impl/utils/paramsResolvers/paramsResolverImpl";
import { ProofProviderSerializer } from "../../../proofProviders/impl/utils/serialization/proofProviderSerializer";
import { ProofGenerationContext } from "../../../proofProviders/proofGenerationContext";
import { ConfigurationError } from "../../../proofProviders/proofProviderErrors";
import { UserModelParams } from "../../../proofProviders/userModelParams";

import { EventLogger } from "../../../logging/eventLogger";
import { throwError } from "../../../utils/errors/throwErrors";
import { MessageHandler } from "../../../utils/structures/messageHandler";

import { provideTestSerializer } from "./testProofProviderSerializer";

export interface MockServiceUserModelParams extends UserModelParams {
    proofsToGenerate: string[];
    workerId?: number;
}

export interface MockServiceModelParams extends ModelParams {
    proofsToGenerate: string[];
    workerId: number;
    resolvedWithMockService: boolean;
}

export const mockServiceModelParamsSchema: JSONSchemaType<MockServiceModelParams> =
    {
        title: "MockServiceModelsParameters",
        type: "object",
        properties: {
            proofsToGenerate: {
                type: "array",
                items: { type: "string" },
            },
            workerId: { type: "number" },
            resolvedWithMockService: { type: "boolean" },
            ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
        },
        required: [
            "proofsToGenerate",
            "workerId",
            "resolvedWithMockService",
            ...modelParamsSchema.required,
        ],
        additionalProperties: false,
    };

/**
 * `MockService` parameters resolution does 4 changes to `inputParams`:
 * - resolves undefined `workerId` to 0;
 * - adds extra `resolvedWithMockService: true` property;
 * - overrides original `systemPrompt` with `this.systemPromptToOverrideWith`;
 * - overrides original `choices` to `defaultChoices` with `proofsToGenerate.length`.
 */
export class MockServiceModelParamsResolver
    extends BasicModelParamsResolver<
        MockServiceUserModelParams,
        MockServiceModelParams
    >
    implements
        ValidParamsResolverImpl<
            MockServiceUserModelParams,
            MockServiceModelParams
        >
{
    constructor() {
        super(mockServiceModelParamsSchema, "MockServiceModelParams");
    }

    readonly proofsToGenerate = this.resolveParam<string[]>("proofsToGenerate")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be non-empty"]);

    readonly workerId = this.resolveParam<number>("workerId")
        .default(() => 0)
        .validate([(value) => value >= 0, "be non-negative"]);

    readonly resolvedWithMockService = this.insertParam<boolean>(
        () => true
    ).validate([(value) => value, "be true"]);

    readonly systemPrompt = this.resolveParam<string>("systemPrompt")
        .override(() => MockService.systemPromptToOverrideWith)
        .requiredToBeConfigured()
        .noValidationNeeded();

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override((inputParams) => inputParams.proofsToGenerate.length)
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}

/**
 * This class implements `ProofProvider` the same way as most of the proofProviders do,
 * so as to reuse the default implementations as much as possible.
 *
 * However, to make tests cover more corner cases, `MockService` provides additional features.
 * Check the documentation of its methods below.
 */
export class MockService extends ProofProvider<
    MockServiceUserModelParams,
    MockServiceModelParams,
    MockService,
    MockServiceGeneratedProof,
    MockServiceInternal
> {
    readonly name = "MockService";
    readonly identifier = undefined;

    protected readonly internal: MockServiceInternal = new MockServiceInternal(
        this
    );
    protected readonly modelParamsResolver =
        new MockServiceModelParamsResolver();
    protected readonly serializer: ProofProviderSerializer =
        provideTestSerializer(
            this.proofProviderSetup,
            (proofProviderParams, controlParams) =>
                new MockService(
                    controlParams.eventLogger,
                    controlParams.errorsHandlingMode,
                    proofProviderParams.generationLogsFilePath
                )
        );

    /**
     * _**Invariant:**_ `MockService` has `debugLogs` always enabled,
     * meaning the generation logs are never cleaned automatically.
     * The cleaning can be done manually via `this.clearGenerationLogs()`.
     */
    constructor(
        eventLogger: EventLogger | undefined,
        errorsHandlingMode: ErrorsHandlingMode,
        generationLogsFilePath: string | undefined = undefined
    ) {
        super({
            eventLogger,
            errorsHandlingMode,
            generationLogsFilePath,
            debugLogs: true,
        });
    }

    static readonly generationFromChatEvent =
        "mock-service-generation-from-chat";

    static readonly systemPromptToOverrideWith =
        "unique mock-service system prompt";

    static readonly proofFixPrompt = "Generate `Fixed.` instead of proof.";
    static readonly fixedProofString = "Fixed.";

    /**
     * Use this method to make 1 next generation (for the specified worker) throw the specified error.
     * Workers are meant to be any external entities that would like to separate their behaviour.
     */
    throwErrorOnNextGeneration(error: Error, workerId: number = 0) {
        this.internal.errorToThrowOnNextGenerationMap.set(workerId, error);
    }

    /**
     * Adds special control message to the chat, so it would make `MockService`
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

export class MockServiceGeneratedProof extends GeneratedProof<
    MockServiceModelParams,
    MockService,
    MockServiceGeneratedProof,
    MockServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockServiceModelParams,
        proofProviderInternal: MockServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal,
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
     * Namely, performs the generation using `ProofProviderInternal.generateFromChatWrapped`.
     */
    async generateNextVersion(
        analyzedChat: AnalyzedChatHistory,
        choices: number,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        abortSignal?: AbortSignal,
        onSchedulerDebugLog: MessageHandler = this.proofProviderInternal
            .sendDebugEventOnSchedulerLog
    ): Promise<MockServiceGeneratedProof[]> {
        return this.proofProviderInternal.generateFromChatWrapped(
            this.modelParams,
            choices,
            metadataHolder,
            abortSignal,
            onSchedulerDebugLog,
            () => {
                if (!this.nextVersionCanBeGenerated()) {
                    throw new ConfigurationError(
                        `next version could not be generated: version ${this.versionNumber} >= max rounds number ${this.maxRoundsNumber}`
                    );
                }
                return analyzedChat;
            },
            (rawProof) =>
                this.proofProviderInternal.constructGeneratedProof(
                    rawProof,
                    this.proofGenerationContext,
                    this.modelParams,
                    this.proofVersions
                )
        );
    }
}

class MockServiceInternal extends ProofProviderInternal<
    MockServiceModelParams,
    MockService,
    MockServiceGeneratedProof,
    MockServiceInternal
> {
    errorToThrowOnNextGenerationMap: Map<number, Error | undefined> = new Map();

    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockServiceModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): MockServiceGeneratedProof {
        return new MockServiceGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams as MockServiceModelParams,
            this,
            previousProofVersions
        );
    }

    // TODO: use `SchedulersProviderBuilders.limitParallelismForModelsWithSameKey` and test it
    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
        );

    /**
     * Generally, `generateFromChatImpl` simply returns first `choices` proofs from the `MockServiceModelParams.proofsToGenerate`.
     * Each `generateFromChatImpl` call sends logic `this.generationFromChatEvent` event to the `eventLogger`.
     * Special behaviour:
     * - If `throwErrorOnNextGenereation` was registered for `MockServiceModelParams.workerId`,
     *   `generateFromChatImpl` throws this error and then resets this behaviour for the next call.
     * - If `chat` contains special control message (see `transformChatToSkipFirstNProofs`),
     *   several proofs from the beggining of `MockServiceModelParams.proofsToGenerate` will be skipped.
     *   Practically, it provides a way to generate different proofs depending on the `chat` (while `modelParams` stay the same).
     * - If `chat` contains `this.proofFixPrompt` in any of its messages,
     *   then all the generated proofs will be equal to `this.fixedProofString`.
     */
    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: MockServiceModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        const chat = analyzedChat.chat;
        this.eventLogger?.logLogicEvent(
            MockService.generationFromChatEvent,
            chat
        );

        const errorToThrow = this.errorToThrowOnNextGenerationMap.get(
            params.workerId
        );
        if (errorToThrow !== undefined) {
            try {
                throw errorToThrow;
            } finally {
                this.errorToThrowOnNextGenerationMap.set(
                    params.workerId,
                    undefined
                );
            }
        }

        const proofFixPromptInChat = chat.find(
            (message) => message.content === MockService.proofFixPrompt
        );
        if (proofFixPromptInChat !== undefined) {
            return ProofProviderInternal.aggregateToGeneratedRawContent(
                Array(choices).fill(MockService.fixedProofString),
                analyzedChat.estimatedTokens?.messagesTokens,
                undefined
            );
        }

        const lastChatMessage = chat[chat.length - 1];
        const skipFirstNProofsParsed =
            this.parseSkipFirstNProofsIfMatches(lastChatMessage);
        const skipFirstNProofs =
            skipFirstNProofsParsed !== undefined ? skipFirstNProofsParsed : 0;

        const proofsLength = params.proofsToGenerate.length - skipFirstNProofs;
        if (choices > proofsLength) {
            throwError(
                `\`choices = ${choices}\` > \`available proofs length = ${proofsLength}\``
            );
        }

        return ProofProviderInternal.aggregateToGeneratedRawContent(
            params.proofsToGenerate.slice(
                skipFirstNProofs,
                skipFirstNProofs + choices
            ),
            analyzedChat.estimatedTokens?.messagesTokens,
            undefined
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
