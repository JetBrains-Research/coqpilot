import { EventLogger, Severity } from "../../logging/eventLogger";
import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
} from "../llmServiceErrors";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory } from "./commonStructures/chat";
import { ErrorsHandlingMode } from "./commonStructures/errorsHandlingMode";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "./commonStructures/generatedRawContent";
import {
    GenerationTokens,
    constructGenerationTokens,
    sumGenerationTokens,
} from "./commonStructures/generationTokens";
import {
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "./commonStructures/llmServiceRequest";
import { ProofVersion } from "./commonStructures/proofVersion";
import { GeneratedProofImpl } from "./generatedProof";
import { LLMServiceImpl } from "./llmService";
import { ModelParams } from "./modelParams";
import { TokensCounter } from "./utils/chatTokensFitter";
import { GenerationsLogger } from "./utils/generationsLogger/generationsLogger";

/**
 * This class represents the inner resources and implementations of `LLMServiceImpl`.
 *
 * Its main goals are to:
 * - separate an actual logic and implementation wrappers from the facade `LLMServiceImpl` class;
 * - make `GeneratedProofImpl` effectively an inner class of `LLMServiceImpl`,
 *   capable of reaching its internal resources.
 *
 * Also, `LLMServiceInternal` is capable of
 * mantaining the `LLMServiceImpl`-s resources and disposing them in the end.
 */
export abstract class LLMServiceInternal<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMServiceImpl<
        UserModelParams,
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    GeneratedProofType extends GeneratedProofImpl<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    LLMServiceInternalType extends LLMServiceInternal<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
> {
    readonly eventLogger: EventLogger | undefined;
    readonly generationsLogger: GenerationsLogger;
    readonly debug: DebugWrappers;

    constructor(
        readonly llmService: LLMServiceType,
        eventLoggerGetter: () => EventLogger | undefined,
        generationsLoggerBuilder: () => GenerationsLogger
    ) {
        this.eventLogger = eventLoggerGetter();
        this.generationsLogger = generationsLoggerBuilder();
        this.debug = new DebugWrappers(
            llmService.serviceName,
            this.eventLogger
        );
    }

    /**
     * Basically, this method should just call the constructor
     * of the corresponding implementation of the `GeneratedProofImpl`.
     * It is needed only to link the service and its proof properly.
     */
    abstract constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ResolvedModelParams,
        previousProofVersions?: ProofVersion[]
    ): GeneratedProofType;

    /**
     * This method should be mostly a pure implementation of
     * the generation from chat, namely, its happy path.
     * This function does not need to handle errors!
     *
     * In case something goes wrong on the side of the external API, any error can be thrown.
     *
     * However, if the generation failed due to the invalid configuration of the request
     * on the CoqPilot's side (for example: invalid token in `params`),
     * this implementation should through `ConfigurationError` whenever possible.
     * It is not mandatory, but that way the user will be notified in a clearer way.
     *
     * Important note: `ResolvedModelParams` are expected to be already validated by `LLMServiceImpl.resolveParameters`,
     * so there is no need to perform this checks again. Report `ConfigurationError` only if something goes wrong during generation runtime.
     *
     * Subnote: most likely, you'd like to call `this.validateChoices` to validate `choices` parameter.
     * Since it overrides `choices`-like parameters of already validated `params`, it might have any number value.
     */
    abstract generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: ResolvedModelParams,
        choices: number
    ): Promise<GeneratedRawContent>;

    /**
     * All the resources that `LLMServiceInternal` is responsible for should be disposed.
     * But only them!
     * For example, `this.generationsLogger` is created and maintained by `LLMServiceInternal`,
     * so it should be disposed in this method.
     * On the contrary, `this.eventLogger` is maintained by the external classes,
     * it is only passed to the `LLMServiceImpl`; thus, it should not be disposed here.
     */
    dispose(): void {
        this.generationsLogger.dispose();
    }

    /**
     * Helper function that wraps `LLMServiceInternal.generateFromChatImpl` call with
     * logging and errors handling.
     *
     * To know more about the latter,
     * check `LLMServiceInternal.logGenerationAndHandleErrors` docs.
     */
    readonly generateFromChatWrapped = async <T>(
        params: ResolvedModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode,
        buildAndValidateChat: () => AnalyzedChatHistory,
        wrapRawProofContent: (proof: string) => T
    ): Promise<T[]> => {
        return this.logGenerationAndHandleErrors<T>(
            params,
            choices,
            errorsHandlingMode,
            (request) => {
                request.analyzedChat = buildAndValidateChat();
            },
            async (request) => {
                return this.generateFromChatImpl(
                    request.analyzedChat!,
                    params,
                    choices
                );
            },
            wrapRawProofContent
        );
    };

    /**
     * This is a helper function that wraps the implementation calls,
     * providing generation logging and errors handling.
     * Many `LLMServiceImpl` invariants are provided by this function;
     * thus, its implementation is final.
     * It should be called only in `LLMServiceImpl` or `GeneratedProofImpl`,
     * to help with overriding the default public methods implementation.
     *
     * Invariants TL;DR:
     * - any thrown error will be of `LLMServiceError` type: if the error is not of that type originally, it'd be wrapped;
     * - errors are rethrown only in case of `RETHROW_ERRORS`;
     * - `this.generationsLogger` logs every success and only `GenerationFailedError`-s (not `ConfigurationError`-s, for example);
     * - `this.eventLogger` logs every success and in case of `LOG_EVENTS_AND_SWALLOW_ERRORS` logs any error;
     *   in case of success / failure event's `data` is the `LLMServiceRequestSucceeded` / `LLMServiceRequestFailed` object respectively.
     *
     * Invariants, the full version.
     * - `completeAndValidateRequest` should fill the received request (for example, with `AnalyzedChatHistory`) and validate its properties;
     *   it is allowed to throw any error:
     *     - if it is not `ConfigurationError` already, its message will be wrapped into `ConfigurationError`;
     *     - then, it will be handled according to `errorsHandlingMode` `(*)`;
     * - If the request is successfully built, then the proofs generation will be performed.
     *     - If no error is thrown:
     *         - generation will be logged as successful one via `this.generationsLogger`;
     *         - `LLMService.requestSucceededEvent` (with `LLMServiceRequestSucceeded` as data) will be logged via `this.eventLogger`.
     *     - If error is thrown:
     *         - it will be wrapped into `GenerationFailedError`, if it is not of `LLMServiceError` type already;
     *         - if it's an instance of `GenerationFailedError`, it will be logged via `this.generationsLogger`;
     *         - finally, it will be handled according to `errorsHandlingMode` `(*)`.
     *
     * `(*)` means:
     * - if `errorsHandlingMode === ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS`,
     *     - `LLMService.requestFailedEvent` (with `LLMServiceRequestFailed` as data
     *       containing the error wrapped into `LLMServiceError`) will be logged via `this.eventLogger`;
     *     - the error will not be rethrown.
     * - if `errorsHandlingMode === ErrorsHandlingMode.RETHROW_ERRORS`,
     *     - the error will be rethrown.
     */
    readonly logGenerationAndHandleErrors = async <T>(
        params: ResolvedModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode,
        completeAndValidateRequest: (request: LLMServiceRequest) => void,
        generateProofs: (
            request: LLMServiceRequest
        ) => Promise<GeneratedRawContent>,
        wrapRawProofContent: (proof: string) => T
    ): Promise<T[]> => {
        const request: LLMServiceRequest = {
            llmService: this.llmService,
            params: params,
            choices: choices,
        };
        try {
            completeAndValidateRequest(request);
        } catch (e) {
            const error = LLMServiceInternal.asErrorOrRethrow(e);
            const configurationError =
                error instanceof ConfigurationError
                    ? error
                    : new ConfigurationError(error.message);
            this.logAndHandleError(
                configurationError,
                errorsHandlingMode,
                request
            );
            return [];
        }
        try {
            const rawGeneratedContent = await generateProofs(request);
            this.logSuccess(request, rawGeneratedContent);
            return rawGeneratedContent.items.map((rawProof) =>
                wrapRawProofContent(rawProof.content)
            );
        } catch (e) {
            const error = LLMServiceInternal.asErrorOrRethrow(e);
            this.logAndHandleError(error, errorsHandlingMode, request);
            return [];
        }
    };

    /**
     * Helper function to handle unsupported method properly.
     */
    unsupportedMethod(
        message: string,
        params: ResolvedModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode
    ) {
        const request: LLMServiceRequest = {
            llmService: this.llmService,
            params: params,
            choices: choices,
        };
        this.logAndHandleError(
            new ConfigurationError(message),
            errorsHandlingMode,
            request
        );
    }

    /**
     * Helper function to validate `choices` are positive.
     *
     * It is not used in the default implementations, since services
     * might handle negative or zero `choices` in some special way.
     * However, this validation is most likely needed in any normal `LLMServiceInternal` implementation.
     */
    static validateChoices(choices: number) {
        if (choices <= 0) {
            throw new ConfigurationError("choices number should be positive");
        }
    }

    /**
     * Helper function to build `GeneratedRawContent` from the generated raw strings.
     *
     * By default, this method builds `GeneratedRawContent` with tokens metrics being estimated **approximately**.
     * Total metrics can be overriden with the `overrideTokensSpentInTotal` parameter.
     */
    static aggregateToGeneratedRawContent(
        rawContentItems: string[],
        perItemPromptTokens: number,
        modelName: string | undefined,
        overrideTokensSpentInTotal: Partial<GenerationTokens> = {}
    ): GeneratedRawContent {
        const tokensCounter = new TokensCounter(modelName);
        try {
            const builtItems: GeneratedRawContentItem[] = rawContentItems.map(
                (content) => {
                    return {
                        content: content,
                        tokensSpent: constructGenerationTokens(
                            perItemPromptTokens,
                            tokensCounter.countTokens(content)
                        ),
                    };
                }
            );
            const builtContent = {
                items: builtItems,
                tokensSpentInTotal: sumGenerationTokens(
                    builtItems.map((item) => item.tokensSpent)
                ),
            };
            builtContent.tokensSpentInTotal = {
                ...builtContent.tokensSpentInTotal,
                ...overrideTokensSpentInTotal,
            };
            return builtContent;
        } finally {
            tokensCounter.dispose();
        }
    }

    private logSuccess(
        request: LLMServiceRequest,
        generatedProofsAsRawContent: GeneratedRawContent
    ) {
        const requestSucceeded: LLMServiceRequestSucceeded = {
            ...request,
            generatedRawProofs: generatedProofsAsRawContent.items,
            tokensSpentInTotal: generatedProofsAsRawContent.tokensSpentInTotal,
        };
        this.generationsLogger.logGenerationSucceeded(requestSucceeded);
        this.eventLogger?.logLogicEvent(
            LLMServiceImpl.requestSucceededEvent,
            requestSucceeded
        );
    }

    private static asErrorOrRethrow(e: any): Error {
        const error = e as Error;
        if (error === null) {
            throw e;
        }
        return error;
    }

    private logAndHandleError(
        error: Error,
        errorsHandlingMode: ErrorsHandlingMode,
        request: LLMServiceRequest
    ) {
        const requestFailed: LLMServiceRequestFailed = {
            ...request,
            llmServiceError:
                error instanceof LLMServiceError
                    ? error
                    : new GenerationFailedError(error),
        };
        if (requestFailed.llmServiceError instanceof GenerationFailedError) {
            this.generationsLogger.logGenerationFailed(requestFailed);
        }
        this.logAsEventOrRethrow(requestFailed, errorsHandlingMode);
    }

    private logAsEventOrRethrow(
        requestFailed: LLMServiceRequestFailed,
        errorsHandlingMode: ErrorsHandlingMode
    ) {
        switch (errorsHandlingMode) {
            case ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS:
                if (!this.eventLogger) {
                    throw Error("cannot log events: no `eventLogger` provided");
                }
                this.eventLogger.logLogicEvent(
                    LLMServiceImpl.requestFailedEvent,
                    requestFailed
                );
                return;
            case ErrorsHandlingMode.RETHROW_ERRORS:
                throw requestFailed.llmServiceError;
            default:
                throw Error(
                    `unsupported \`ErrorsHandlingMode\`: ${errorsHandlingMode}`
                );
        }
    }
}

/**
 * Helper object that provides wrappers to write debug logs shorter.
 *
 * Its instance is available inside `LLMServiceInternal` and
 * could be passed into other classes of the internal implementation.
 */
export class DebugWrappers {
    constructor(
        private readonly serviceName: string,
        private readonly eventLogger?: EventLogger
    ) {}

    /**
     * Helper method that provides debug logging in a shorter way.
     */
    logEvent(message: string, data?: any) {
        this.eventLogger?.log(this.serviceName, message, data, Severity.DEBUG);
    }
}
