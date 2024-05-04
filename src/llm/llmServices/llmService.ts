import * as tmp from "tmp";

import { EventLogger } from "../../logging/eventLogger";
import {
    ConfigurationError,
    GenerationFailedError,
    LLMServiceError,
} from "../llmServiceErrors";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory, ChatHistory } from "./chat";
import { ModelParams } from "./modelParams";
import {
    buildProofFixChat,
    buildProofGenerationChat,
} from "./utils/chatFactory";
import { estimateTimeToBecomeAvailableDefault } from "./utils/defaultAvailabilityEstimator";
import { resolveParametersWithDefaultsImpl } from "./utils/defaultParametersResolver";
import {
    FromChatGenerationRequest,
    GenerationRequest,
    GenerationsLogger,
} from "./utils/requestsLogger/generationsLogger";
import { LoggerRecord } from "./utils/requestsLogger/loggerRecord";
import { Time } from "./utils/time";

export type Proof = string;

export interface ProofVersion {
    proof: Proof;
    diagnostic?: string;
}

/* eslint-disable @typescript-eslint/naming-convention */
export enum ErrorsHandlingMode {
    LOG_EVENTS_AND_SWALLOW_ERRORS = "log events & swallow errors",
    RETHROW_ERRORS = "rethrow errors",
}

/**
 * `LLMService` represents a service for proofs generation.
 * Proofs can be generated from both `ProofGenerationContext` and `AnalyzedChatHistory`.
 * Generated proofs are represented by `GeneratedProof` class and
 * can be further regenerated (fixed / shortened / etc), also keeping their previous versions.
 *
 * All proofs-generation methods support errors handling and logging.
 * - Each successfull generation is logged both by `GenerationsLogger` and `EventsLogger`.
 * - If error occurs, it is catched and then:
 *   - in case of <LOG_EVENTS_AND_SWALLOW_ERRORS>, it's only logged by `EventsLogger`;
 *   - in case of <RETHROW_ERRORS>, it's wrapped into `LLMServiceError` and then rethrown.
 * `EventsLogger` sends `generationRequestSucceededEvent` and `generationRequestFailedEvent`,
 * which can be handled then, for example, by the UI.
 * `GenerationsLogger` maintains the logs used for the further estimation of the service availability
 * See the `estimateTimeToBecomeAvailable` method.
 *
 * Moreover, `LLMService` is capable of resolving partially-undefined `UserModelParams`
 * to complete `ModelParams`. See the `resolveParameters` method.
 *
 * To implement a new `LLMService` based on generating proofs from chats, one should:
 * - declare custom `GeneratedProof`;
 * - implement custom `LLMServiceInternal`;
 * - finally, declare custom `LLMService`.
 * I.e. `LLMServiceInternal` is effectively the only interface needed to be actually implemented.
 *
 * If proofs-generation is not supposed to be based on chats,
 * the methods of `LLMService` should be overriden directly.
 */
export abstract class LLMService {
    protected abstract readonly internal: LLMServiceInternal;
    protected readonly eventLoggerGetter: () => EventLogger | undefined;
    protected readonly generationsLoggerBuilder: () => GenerationsLogger;

    /**
     * Creates an instance of `LLMService`.
     * @param eventLogger if it is not specified, events won't be logged and passing `LOG_EVENTS_AND_SWALLOW_ERRORS` will throw an error.
     * @param debug enables debug logs for the internal `GenerationsLogger`.
     * @param generationLogsFilePath if it is not specified, a temporary file will be used.
     */
    constructor(
        readonly serviceName: string,
        eventLogger: EventLogger | undefined,
        debug: boolean,
        generationLogsFilePath: string | undefined
    ) {
        this.eventLoggerGetter = () => eventLogger;
        this.generationsLoggerBuilder = () =>
            new GenerationsLogger(
                generationLogsFilePath ?? tmp.fileSync().name,
                debug
            );
    }

    static readonly generationRequestSucceededEvent = `generation-request-succeeded`;
    static readonly generationRequestFailedEvent = `generation-request-failed`;

    /**
     * Generates proofs from chat. This method performs errors-handling and logging, check `LLMService` docs for more details.
     *
     * @returns generated raw proofs as strings.
     */
    async generateFromChat(
        analyzedChat: AnalyzedChatHistory,
        params: ModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<string[]> {
        return this.internal.logGenerationAndHandleErrors(
            () => {
                return {
                    chat: analyzedChat.chat,
                    estimatedTokens: analyzedChat.estimatedTokens,
                    params: params,
                    choices: choices,
                } as FromChatGenerationRequest;
            },
            async (_request: GenerationRequest) => {
                return await this.internal.generateFromChatImpl(
                    analyzedChat.chat,
                    params,
                    choices
                );
            },
            (proof) => proof,
            errorsHandlingMode
        );
    }

    /**
     * Generates proofs from `ProofGenerationContext`, i.e. from `completionTarget` and `contextTheorems`.
     * This method performs errors-handling and logging, check `LLMService` docs for more details.
     *
     * The default implementation is based on the generation from chat, namely,
     * it calls `LLMServiceInternal.generateFromChatImpl`.
     * If it is not the desired way, this method should be overriden.
     *
     * @returns generated proofs as `GeneratedProof`-s.
     */
    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<GeneratedProof[]> {
        return this.internal.logGenerationAndHandleErrors(
            () => {
                const analyzedChat = buildProofGenerationChat(
                    proofGenerationContext,
                    params
                );
                return {
                    chat: analyzedChat.chat,
                    estimatedTokens: analyzedChat.estimatedTokens,
                    params: params,
                    choices: choices,
                } as FromChatGenerationRequest;
            },
            async (request: GenerationRequest) => {
                const proofs = await this.internal.generateFromChatImpl(
                    (request as FromChatGenerationRequest).chat,
                    params,
                    choices
                );
                return proofs.map((proof) =>
                    this.internal.constructGeneratedProof(
                        proof,
                        proofGenerationContext,
                        params
                    )
                );
            },
            (generatedProof: GeneratedProof) => generatedProof.proof(),
            errorsHandlingMode
        );
    }

    /**
     * Estimates the expected time for service to become available.
     * To do this, analyzes the logs from `this.generationsLogger` and computes the time.
     */
    estimateTimeToBecomeAvailable(): Time {
        return estimateTimeToBecomeAvailableDefault(
            this.internal.generationsLogger.readLogsSinceLastSuccess()
        );
    }

    /**
     * Reads logs provided by `GenerationsLogger` for this service.
     */
    readGenerationsLogs(sinceLastSuccess: boolean = false): LoggerRecord[] {
        return sinceLastSuccess
            ? this.internal.generationsLogger.readLogsSinceLastSuccess()
            : this.internal.generationsLogger.readLogs();
    }

    dispose(): void {
        this.internal.dispose();
    }

    /**
     * Resolves possibly-incomplete `UserModelParams` to complete `ModelParams`.
     * If it is not possible, an error will be thrown.
     *
     * First, parameters might be resolved by `LLMService` implementation,
     * then everything unresolved is resolved with defaults (by `resolveParametersWithDefaults` method).
     * Thus, any implementation of this method should call `resolveParametersWithDefaults` at the end.
     *
     * @param params possibly-incomplete parameters configured by user.
     * @returns complete parameters for the further generation pipeline.
     */
    resolveParameters(params: UserModelParams): ModelParams {
        return this.resolveParametersWithDefaults(params);
    }

    protected readonly resolveParametersWithDefaults = (
        params: UserModelParams
    ): ModelParams => resolveParametersWithDefaultsImpl(params);
}

/**
 * This class represents the inner resources and implementations of `LLMService`.
 *
 * Its main goals are to:
 * - separate an actual logic from the facade `LLMService` class;
 * - make `GeneratedProof` effectively an inner class of `LLMService`,
 * capable of reaching its internal resources.
 *
 * Also, `LLMServiceInternal` is capable of
 * mantaining the `LLMService`-s resources and disposing them in the end.
 */
export abstract class LLMServiceInternal {
    readonly eventLogger: EventLogger | undefined;
    readonly generationsLogger: GenerationsLogger;

    constructor(
        readonly llmService: LLMService,
        eventLoggerGetter: () => EventLogger | undefined,
        generationsLoggerBuilder: () => GenerationsLogger
    ) {
        this.eventLogger = eventLoggerGetter();
        this.generationsLogger = generationsLoggerBuilder();
    }

    /**
     * Basically, this method should just call the constructor
     * of the corresponding implementation of the `GeneratedProof`.
     * It is needed only to link the service and its proof properly.
     */
    abstract constructGeneratedProof(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[]
    ): GeneratedProof;

    /**
     * This method should be mostly a pure implementation of
     * the generation from chat, namely, its happy path.
     * This function doesn't need to handle errors!
     *
     * However, if the configuration of the request on the CoqPilot's side
     * is invalid in any sense (for example: invalid token in `params`, bad `choices` number, etc),
     * this implementation should through `ConfigurationError` whenever possible.
     * It is not mandatory, but that way the user will be notified in a clearer way.
     * In case something goes wrong on the side of the external API, any error can be thrown.
     */
    abstract generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]>;

    /**
     * All the resources that `LLMServiceInternal` is responsible for should be disposed.
     * But only them!
     * For example, `this.requestsLogger` is created and maintained by `LLMServiceInternal`,
     * so it should be disposed in this method.
     * On the contrary, `this.eventLogger` is maintained by the external classes,
     * it is only passed to the `LLMService`; thus, it should not be disposed here.
     */
    dispose(): void {
        this.generationsLogger.dispose();
    }

    /**
     * This is a helper function that wraps the implementation calls,
     * providing generation logging and errors handling.
     * Many `LLMService` invariants are provided by this function;
     * thus, it is final.
     * It should be called only in `LLMService` or `GeneratedProof`,
     * to help with overriding the default public methods implementation.
     *
     * Invariants TL;DR:
     * - `this.generationsLogger` logs only generation errors or success and not `ConfigurationError`-s;
     * - `this.eventsLogger` always logs every success and logs any error in case of `LOG_EVENTS_AND_SWALLOW_ERRORS`;
     * - errors are rethrown only in case of `RETHROW_ERRORS`;
     * - any thrown error will be of `LLMServiceError` type: if the error is not of that type originally, it'd be wrapped.
     *
     * Invariants, the full version.
     * - `buildAndValidateRequest` can throw any error:
     *     - if it is not `ConfigurationError` already, its message will be wrapped into `ConfigurationError`;
     *     - then, it will be handled according to `errorsHandlingMode` (*);
     * - If the request is successfully built, then the proofs generation will be performed.
     *     - If no error is thrown:
     *         - generation will be logged as successful one via `this.generationsLogger`;
     *         - `LLMService.generationRequestSucceededEvent` (with `this` as data) will be logged via `this.eventsLogger`.
     *     - If `ConfigurationError` is thrown, it will be handled according to `errorsHandlingMode` (*).
     *     - Otherwise:
     *         - generation will be logged as failed one via `this.generationsLogger`;
     *         - the error will be wrapped into `GenerationFailedError` (if it is not of this type already);
     *         - it will be handled according to `errorsHandlingMode` (*).
     *
     * (*) means:
     * - if `errorsHandlingMode === ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS`,
     *     - `LLMService.generationRequestFailedEvent` (with `[this, error]` as data) will be logged via `this.eventsLogger`.
     *     - the error will not be rethrown.
     * - if `errorsHandlingMode === ErrorsHandlingMode.RETHROW_ERRORS`,
     *     - the error will be rethrown.
     */
    readonly logGenerationAndHandleErrors = async <T>(
        buildAndValidateRequest: () => GenerationRequest,
        generateProofs: (request: GenerationRequest) => Promise<T[]>,
        getRawProof: (generatedProof: T) => string,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<T[]> => {
        const buildAndValidateRequestHandled = () => {
            try {
                return buildAndValidateRequest();
            } catch (e) {
                const error = LLMServiceInternal.asError(e);
                let configurationError =
                    error instanceof ConfigurationError
                        ? error
                        : new ConfigurationError(error.message);
                this.handleError(configurationError, errorsHandlingMode);
                return undefined;
            }
        };
        const request = buildAndValidateRequestHandled();
        if (request === undefined) {
            return [];
        }

        try {
            const generatedProofs = await generateProofs(request);
            this.generationsLogger.logGenerationSucceeded(
                request,
                generatedProofs.map(getRawProof)
            );
            this.eventLogger?.logLogicEvent(
                LLMService.generationRequestSucceededEvent,
                this.llmService
            );
            return generatedProofs;
        } catch (e) {
            const error = LLMServiceInternal.asError(e);
            if (error instanceof ConfigurationError) {
                this.handleError(error, errorsHandlingMode);
            } else {
                this.generationsLogger.logGenerationFailed(request, error);
                this.handleError(
                    error instanceof GenerationFailedError
                        ? error
                        : new GenerationFailedError(error),
                    errorsHandlingMode
                );
            }
            return [];
        }
    };

    private handleError(
        llmServiceError: LLMServiceError,
        errorsHandlingMode: ErrorsHandlingMode
    ) {
        switch (errorsHandlingMode) {
            case ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS:
                if (!this.eventLogger) {
                    throw Error("cannot log events: no `eventLogger` provided");
                }
                this.eventLogger.logLogicEvent(
                    LLMService.generationRequestFailedEvent,
                    [this.llmService, llmServiceError]
                );
                return;
            case ErrorsHandlingMode.RETHROW_ERRORS:
                throw llmServiceError;
            default:
                throw Error(
                    `unsupported \`ErrorsHandlingMode\`: ${errorsHandlingMode}`
                );
        }
    }

    private static asError(e: any): Error {
        const error = e as Error;
        if (error === null) {
            throw e;
        }
        return error;
    }
}

/**
 * This class represents a proof generated by `LLMService`.
 * It stores all the meta information of its generation.
 *
 * Moreover, it might support regeneration: fixing, shortening, etc.
 * For this, a new version of this proof could be generated via `LLMServiceInternal.generateFromChat`.
 *
 * Regeneration (in other words, multiround-generation) parameters are specified at `ModelParams.multiroundProfile`.
 *
 * Same to `LLMService`, regeneration methods performs errors handling and logging (in the same way).
 * Same to `LLMService`, these methods could be overriden to change the regeneration behaviour.
 *
 * Finally, `GeneratedProof` keeps the previous proof versions (but not the future ones).
 */
export abstract class GeneratedProof {
    /**
     * An accessor for `ModelParams.multiroundProfile.maxRoundsNumber`.
     */
    readonly maxRoundsNumber: number;

    /**
     * Previous proof versions of the current `GeneratedProof` (including the latest one).
     * Only the last one (i.e. the latest) is allowed to have an incomplete `ProofVersion`.
     *
     * When this `GeneratedProof` is regenerated (for example, `fixProof` is called),
     * the `proofVersions` won't track the results (newer proof versions).
     * Completely new `GeneratedProof` objects will be returned,
     * having longer `proofVersions` stored inside.
     */
    readonly proofVersions: ProofVersion[];

    /**
     * Creates an instance of `GeneratedProof`.
     * Should be called only by `LLMService`, `LLMServiceInternal` or `GeneratedProof` itself.
     */
    constructor(
        proof: Proof,
        readonly proofGenerationContext: ProofGenerationContext,
        readonly modelParams: ModelParams,
        protected readonly llmServiceInternal: LLMServiceInternal,
        previousProofVersions: ProofVersion[] = []
    ) {
        // Makes a copy of the previous proof versions
        this.proofVersions = [...previousProofVersions];
        this.proofVersions.push({
            proof: proof,
            diagnostic: undefined,
        });

        this.maxRoundsNumber =
            this.modelParams.multiroundProfile.maxRoundsNumber;
        if (this.maxRoundsNumber < this.proofVersions.length) {
            throw new Error(
                `proof cannot be generated: max rounds number (${this.maxRoundsNumber}) was already reached`
            );
        }
    }

    /**
     * @returns proof of the latest version for this `GeneratedProof`.
     */
    proof(): Proof {
        return this.lastProofVersion().proof;
    }

    protected lastProofVersion(): ProofVersion {
        return this.proofVersions[this.proofVersions.length - 1];
    }

    /**
     * Initially generated proofs has version number equal to 1.
     * Each regeneration (multiround generation) creates `GeneratedProofs`
     * with version = `this.versionNumber() + 1`.
     *
     * @returns version number of this `GeneratedProof`.
     */
    versionNumber(): number {
        return this.proofVersions.length;
    }

    /**
     * This method doesn't check `ModelParams.multiroundProfile.fixedProofChoices`,
     * because they can be overriden via the function's parameters at the call.
     *
     * @returns whether this `GeneratedProof` is allowed to be fixed at least once.
     */
    canBeFixed(): Boolean {
        return this.nextVersionCanBeGenerated();
    }

    /**
     * @returns whether `maxRoundsNumber` allows to generate a newer version of this proof.
     */
    protected nextVersionCanBeGenerated(): Boolean {
        return this.versionNumber() < this.maxRoundsNumber;
    }

    /**
     * Generates new `GeneratedProof`-s as fixes for the latest version of the current one.
     * This method performs errors-handling and logging the same way as `LLMService`'s methods do.
     *
     * When this method is called, the `diagnostic` of the latest proof version
     * is overwritten with the `diagnostic` parameter of the call.
     *
     * @param diagnostic diagnostic received from the compiler.
     * @param choices if specified, overrides `ModelParams.multiroundProfile.fixedProofChoices`.
     */
    async fixProof(
        diagnostic: string,
        choices: number = this.modelParams.multiroundProfile.proofFixChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<GeneratedProof[]> {
        return this.llmServiceInternal.logGenerationAndHandleErrors(
            () => {
                if (!this.canBeFixed()) {
                    throw new ConfigurationError(
                        `this \`GeneratedProof\` could not be fixed: version ${this.versionNumber()} >= max rounds number ${this.maxRoundsNumber}`
                    );
                }
                this.lastProofVersion().diagnostic = diagnostic;

                const analyzedChat = buildProofFixChat(
                    this.proofGenerationContext,
                    this.proofVersions,
                    this.modelParams
                );
                return {
                    chat: analyzedChat.chat,
                    estimatedTokens: analyzedChat.estimatedTokens,
                    params: this.modelParams,
                    choices: choices,
                } as FromChatGenerationRequest;
            },
            async (request: GenerationRequest) => {
                const newProofs =
                    await this.llmServiceInternal.generateFromChatImpl(
                        (request as FromChatGenerationRequest).chat,
                        this.modelParams,
                        choices
                    );
                return newProofs.map((proof: string) =>
                    this.llmServiceInternal.constructGeneratedProof(
                        this.removeProofQedIfNeeded(proof),
                        this.proofGenerationContext,
                        this.modelParams,
                        this.proofVersions
                    )
                );
            },
            (generatedProof: GeneratedProof) => generatedProof.proof(),
            errorsHandlingMode
        );
    }

    protected removeProofQedIfNeeded(message: string): string {
        const regex = /Proof\.(.*?)Qed\./s;
        const match = regex.exec(message);
        if (match) {
            return match[0];
        } else {
            return message;
        }
    }
}
