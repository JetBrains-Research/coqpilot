import { EventLogger, Severity } from "../../logging/eventLogger";
import { asErrorOrRethrow } from "../../utils/errors/errorsUtils";
import { createTmpFile } from "../../utils/fs/tmpFs";
import { MessageHandler } from "../../utils/structures/messageHandler";
import { ProofGenerationContext } from "../proofGenerationContext";
import {
    ConfigurationError,
    GenerationFailedError,
    ProofProviderError,
} from "../proofProviderErrors";
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
import { ProofGenerationMetadataHolder } from "./commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "./commonStructures/proofGenerationType";
import {
    ProofProviderRequest,
    ProofProviderRequestFailed,
    ProofProviderRequestSucceeded,
} from "./commonStructures/proofProviderRequest";
import { ProofVersion } from "./commonStructures/proofVersion";
import { SchedulersProvider } from "./commonStructures/schedulersProviders";
import { GeneratedProof } from "./generatedProof";
import { ModelParams } from "./modelParams";
import { ProofProvider } from "./proofProvider";
import { ResolvedProofProviderParams } from "./proofProviderParams";
import { TokensCounter } from "./utils/chatTokensFitter";
import { GenerationsLogger } from "./utils/generationsLogger/generationsLogger";

/**
 * This class represents the inner resources and implementations of `ProofProvider`.
 *
 * Its main goals are to:
 * - separate an actual logic and implementation wrappers from the facade `ProofProvider` class;
 * - make `GeneratedProof` effectively an inner class of `ProofProvider`,
 *   capable of reaching its internal resources.
 *
 * Also, `ProofProviderInternal` is capable of
 * mantaining the `ProofProvider`-s resources and disposing them in the end.
 */
export abstract class ProofProviderInternal<
    ResolvedModelParams extends ModelParams,
    ProofProviderType extends ProofProvider<
        UserModelParams,
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    GeneratedProofType extends GeneratedProof<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    ProofProviderInternalType extends ProofProviderInternal<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
> {
    readonly proofProviderSetup: ResolvedProofProviderParams =
        this.proofProvider.proofProviderSetup;

    readonly eventLogger: EventLogger | undefined =
        this.proofProviderSetup.eventLogger;
    readonly errorsHandlingMode: ErrorsHandlingMode =
        this.proofProviderSetup.errorsHandlingMode;

    readonly generationsLogger: GenerationsLogger;
    readonly logDebug: DebugLogsWrappers;

    constructor(
        readonly proofProvider: ProofProviderType,
        prebuiltGenerationsLogger?: GenerationsLogger
    ) {
        if (prebuiltGenerationsLogger === undefined) {
            const generationLogsFilePath =
                proofProvider.proofProviderSetup.generationLogsFilePath ??
                createTmpFile();
            this.generationsLogger = new GenerationsLogger(
                generationLogsFilePath,
                {
                    debug: proofProvider.proofProviderSetup.debugLogs,
                    paramsPropertiesToCensor: {
                        apiKey: GenerationsLogger.censorString,
                    },
                    cleanLogsOnStart: true,
                }
            );
        } else {
            this.generationsLogger = prebuiltGenerationsLogger;
        }
        this.logDebug = new DebugLogsWrappers(
            proofProvider.name,
            this.eventLogger
        );
    }

    /**
     * Basically, this method should just call the constructor
     * of the corresponding implementation of the `GeneratedProof`.
     * It is needed only to link the proofProvider and its proof properly.
     */
    abstract constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ResolvedModelParams,
        previousProofVersions?: ProofVersion[]
    ): GeneratedProofType;

    /**
     * Maintain schedulers to execute generation task involving given models.
     * `modelsSchedulersProvider` allows to control the maximum parallelism for the models of this `ProofProvider`.
     *
     * Check `SchedulersProviderBuilders` for already available implementations.
     */
    abstract readonly modelsSchedulersProvider: SchedulersProvider;

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
     * Important note: `ResolvedModelParams` are expected to be already validated by `ProofProvider.resolveParameters`,
     * so there is no need to perform this checks again. Report `ConfigurationError` only if something goes wrong during generation runtime.
     *
     * Subnote: most likely, you'd like to call `this.validateChoices` to validate `choices` parameter.
     * Since it overrides `choices`-like properties of already validated `params`, it might have any number value.
     */
    abstract generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: ResolvedModelParams,
        choices: number,
        abortSignal?: AbortSignal
    ): Promise<GeneratedRawContent>;

    /**
     * All the resources that `ProofProviderInternal` is responsible for should be disposed.
     * But only them!
     * For example, `this.generationsLogger` is created and maintained by `ProofProviderInternal`,
     * so it should be disposed in this method.
     * On the contrary, `this.eventLogger` is maintained by the external classes,
     * it is only passed to the `ProofProvider`; thus, it should not be disposed here.
     */
    dispose(): void {
        this.generationsLogger.dispose();
    }

    /**
     * Helper function that wraps a generation task to execute it scheduled
     * with respect to the other generation tasks involving `params` model.
     *
     * Basically, all proof-generation calls should be wrapped into this method
     * to enable the maximum parallelism control, which, in turn, guarantees
     * the whole system progress on high requests workload.
     */
    readonly scheduleGenerationTask = async <T>(
        params: ResolvedModelParams,
        task: () => Promise<T>,
        onDebugLog: MessageHandler
    ): Promise<T> => {
        return this.modelsSchedulersProvider
            .getScheduler(params)
            .scheduleTask(task, onDebugLog);
    };

    /**
     * Helper function that wraps `ProofProviderInternal.generateFromChatImpl` call with
     * generation task scheduling and logging and errors handling.
     *
     * To know more about the latter,
     * check `ProofProviderInternal.logGenerationAndHandleErrors` docs.
     */
    readonly generateFromChatWrapped = async <T>(
        params: ResolvedModelParams,
        choices: number,
        metadataHolder: ProofGenerationMetadataHolder | undefined,
        abortSignal: AbortSignal | undefined,
        onSchedulerDebugLog: MessageHandler,
        buildAndValidateChat: () => AnalyzedChatHistory,
        wrapRawProofContent: (rawProof: GeneratedRawContentItem) => T
    ): Promise<T[]> =>
        this.scheduleLoggedGenerationAndHandleErrors(
            ProofGenerationType.CHAT_BASED,
            params,
            choices,
            metadataHolder,
            onSchedulerDebugLog,
            (request) => {
                request.analyzedChat = buildAndValidateChat();
            },
            async (request) =>
                this.generateFromChatImpl(
                    request.analyzedChat!,
                    params,
                    choices,
                    abortSignal
                ),
            wrapRawProofContent
        );

    /**
     * Helper function that wraps `ProofProviderInternal.logGenerationAndHandleErrors` call
     * with generation task scheduling (i.e. `ProofProviderInternal.scheduleGenerationTask` call).
     */
    readonly scheduleLoggedGenerationAndHandleErrors = async <T>(
        proofGenerationType: ProofGenerationType,
        params: ResolvedModelParams,
        choices: number,
        metadataHolder: ProofGenerationMetadataHolder | undefined,
        onSchedulerDebugLog: MessageHandler,
        completeAndValidateRequest: (request: ProofProviderRequest) => void,
        generateProofs: (
            request: ProofProviderRequest
        ) => Promise<GeneratedRawContent>,
        wrapRawProofContent: (rawProof: GeneratedRawContentItem) => T
    ): Promise<T[]> =>
        this.scheduleGenerationTask(
            params,
            () =>
                this.logGenerationAndHandleErrors(
                    proofGenerationType,
                    params,
                    choices,
                    metadataHolder,
                    completeAndValidateRequest,
                    generateProofs,
                    wrapRawProofContent
                ),
            onSchedulerDebugLog
        );

    /**
     * This is a helper function that wraps the implementation calls,
     * providing generation logging and errors handling.
     * Many `ProofProvider` invariants are provided by this function;
     * thus, its implementation is final.
     * It should be called only in `ProofProvider` or `GeneratedProof`,
     * to help with overriding the default public methods implementation.
     *
     * Invariants TL;DR:
     * - `metadataHolder` is updated with `proofGenerationType` at the very beginning and with the final result metadata in the end;
     * - any thrown error will be of `ProofProviderError` type: if the error is not of that type originally, it'd be wrapped;
     * - errors are rethrown only in case of `RETHROW_ERRORS`;
     * - `this.generationsLogger` logs every success and only `GenerationFailedError`-s (not `ConfigurationError`-s, for example);
     * - `this.eventLogger` logs every success and any error;
     *   in case of success / failure event's `data` is the `ProofProviderRequestSucceeded` / `ProofProviderRequestFailed` object respectively.
     *
     * Invariants, the full version.
     * - `metadataHolder` is updated with `proofGenerationType` at the very beginning;
     * - `completeAndValidateRequest` should fill the received request (for example, with `AnalyzedChatHistory`) and validate its properties;
     *   it is allowed to throw any error:
     *     - if it is not `ConfigurationError` already, its message will be wrapped into `ConfigurationError`;
     *     - then, it will be handled according to `errorsHandlingMode` `(*)`;
     * - If the request is successfully built, then the proofs generation will be performed.
     *     - `metadataHolder` is updated with the built request;
     *     - If no error is thrown:
     *         - generation will be logged as successful one via `this.generationsLogger`;
     *         - `ProofProvider.requestSucceededEvent` (with `ProofProviderRequestSucceeded` as data) will be logged via `this.eventLogger`.
     *         - `metadataHolder` is updated with the success metadata;
     *     - If error is thrown:
     *         - it will be wrapped into `GenerationFailedError`, if it is not of `ProofProviderError` type already;
     *         - if it's an instance of `GenerationFailedError`, it will be logged via `this.generationsLogger`;
     *         - finally, it will be handled according to `errorsHandlingMode` `(*)`.
     *
     * `(*)` means:
     * - `ProofProvider.requestFailedEvent` (with `ProofProviderRequestFailed` as data
     *   containing the error wrapped into `ProofProviderError`) will be logged via `this.eventLogger`;
     * - `metadataHolder` is updated with the failure metadata;
     * - if `this.errorsHandlingMode === ErrorsHandlingMode.RETHROW_ERRORS`,
     *   the error will be rethrown.
     * - if `this.errorsHandlingMode === ErrorsHandlingMode.SWALLOW_ERRORS`,
     *   the error will not be rethrown.
     */
    readonly logGenerationAndHandleErrors = async <T>(
        proofGenerationType: ProofGenerationType,
        params: ResolvedModelParams,
        choices: number,
        metadataHolder: ProofGenerationMetadataHolder | undefined,
        completeAndValidateRequest: (request: ProofProviderRequest) => void,
        generateProofs: (
            request: ProofProviderRequest
        ) => Promise<GeneratedRawContent>,
        wrapRawProofContent: (rawProof: GeneratedRawContentItem) => T
    ): Promise<T[]> => {
        const request: ProofProviderRequest = {
            proofProvider: this.proofProvider,
            proofGenerationType: proofGenerationType,
            params: params,
            choices: choices,
        };
        metadataHolder?.setProofGenerationType(proofGenerationType);
        try {
            completeAndValidateRequest(request);
            metadataHolder?.updateWithBuiltRequest(request);
        } catch (e) {
            const error = asErrorOrRethrow(e);
            const configurationError =
                error instanceof ConfigurationError
                    ? error
                    : new ConfigurationError(error.message);
            this.logAndHandleError(configurationError, request, metadataHolder);
            return [];
        }
        try {
            const rawGeneratedContent = await generateProofs(request);
            this.logSuccess(request, rawGeneratedContent, metadataHolder);
            return rawGeneratedContent.items.map((rawProof) =>
                wrapRawProofContent(rawProof)
            );
        } catch (e) {
            const error = asErrorOrRethrow(e);
            this.logAndHandleError(error, request, metadataHolder);
            return [];
        }
    };

    /**
     * Helper function to handle unsupported method properly.
     */
    unsupportedMethod(
        message: string,
        proofGenerationType: ProofGenerationType,
        params: ResolvedModelParams,
        choices: number
    ) {
        const request: ProofProviderRequest = {
            proofProvider: this.proofProvider,
            proofGenerationType: proofGenerationType,
            params: params,
            choices: choices,
        };
        this.logAndHandleError(
            new ConfigurationError(message),
            request,
            undefined
        );
    }

    /**
     * Helper function to validate `choices` are positive.
     *
     * It is not used in the default implementations, since proofProviders
     * might handle negative or zero `choices` in some special way.
     * However, this validation is most likely needed in any normal `ProofProviderInternal` implementation.
     */
    static validateChoices(choices: number) {
        if (choices <= 0) {
            throw new ConfigurationError(
                `choices number should be positive, but got: ${choices}`
            );
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
        request: ProofProviderRequest,
        generatedProofsAsRawContent: GeneratedRawContent,
        metadataHolder: ProofGenerationMetadataHolder | undefined
    ) {
        const requestSucceeded: ProofProviderRequestSucceeded = {
            ...request,
            generatedRawProofs: generatedProofsAsRawContent.items,
            tokensSpentInTotal: generatedProofsAsRawContent.tokensSpentInTotal,
        };
        this.generationsLogger.logGenerationSucceeded(requestSucceeded);
        this.eventLogger?.logLogicEvent(
            ProofProvider.requestSucceededEvent,
            requestSucceeded
        );
        metadataHolder?.setSuccessMetadata(requestSucceeded);
    }

    private logAndHandleError(
        error: Error,
        request: ProofProviderRequest,
        metadataHolder: ProofGenerationMetadataHolder | undefined
    ) {
        const requestFailed: ProofProviderRequestFailed = {
            ...request,
            proofProviderError:
                error instanceof ProofProviderError
                    ? error
                    : new GenerationFailedError(error),
        };
        if (requestFailed.proofProviderError instanceof GenerationFailedError) {
            this.generationsLogger.logGenerationFailed(requestFailed);
        }
        this.eventLogger?.logLogicEvent(
            ProofProvider.requestFailedEvent,
            requestFailed
        );
        metadataHolder?.setFailureMetadata(requestFailed);
        if (this.errorsHandlingMode === ErrorsHandlingMode.RETHROW_ERRORS) {
            throw requestFailed.proofProviderError;
        }
    }

    readonly sendDebugEventOnSchedulerLog: MessageHandler = (
        schedulerDebugLog: string
    ) => this.logDebug.event(schedulerDebugLog);
}

/**
 * Helper object that provides wrappers to write debug logs shorter.
 *
 * Its instance is available inside `ProofProviderInternal` and
 * could be passed into other classes of the internal implementation.
 */
export class DebugLogsWrappers {
    constructor(
        private readonly proofProviderName: string,
        private readonly eventLogger?: EventLogger
    ) {}

    /**
     * Helper method that provides debug logging in a shorter way.
     */
    event(message: string, data?: any) {
        this.eventLogger?.log(
            this.proofProviderName,
            message,
            data,
            Severity.DEBUG
        );
    }
}
