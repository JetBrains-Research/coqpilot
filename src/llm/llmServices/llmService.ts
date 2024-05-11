import * as tmp from "tmp";

import { EventLogger, Severity } from "../../logging/eventLogger";
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
import { GenerationsLogger } from "./utils/generationsLogger/generationsLogger";
import { LoggerRecord } from "./utils/generationsLogger/loggerRecord";
import { ParamsResolutionResult, ParamsResolver } from "./utils/paramsResolver";
import { Time } from "./utils/time";

export interface ProofVersion {
    proof: string;
    diagnostic?: string;
}

/* eslint-disable @typescript-eslint/naming-convention */
export enum ErrorsHandlingMode {
    LOG_EVENTS_AND_SWALLOW_ERRORS = "log events & swallow errors",
    RETHROW_ERRORS = "rethrow errors",
}

/**
 * Interface for `LLMServiceImpl` to package all generation request data.
 * Then, this data is used for interaction between implementation components.
 * In addition, interfaces derived from it can be passed to loggers to record the requests' results.
 */
export interface LLMServiceRequest {
    llmService: LLMService<any, any>;
    params: ModelParams;
    choices: number;
    analyzedChat?: AnalyzedChatHistory;
}

export interface LLMServiceRequestSucceeded extends LLMServiceRequest {
    generatedRawProofs: string[];
}

export interface LLMServiceRequestFailed extends LLMServiceRequest {
    llmServiceError: LLMServiceError;
}

/**
 * Facade type for the `LLMServiceImpl<InputModelParams, ResolvedModelParams, LLMServiceInternalType>` type.
 *
 * Proper typing of `LLMServiceImpl.internal` is required inside implementations only;
 * thus, `LLMServiceImpl` should be resolved with `any` as `LLMServiceInternalType` when used outside.
 */
export type LLMService<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
> = LLMServiceImpl<InputModelParams, ResolvedModelParams, any>;

/**
 * `LLMServiceImpl` represents a service for proofs generation.
 * Proofs can be generated from both `ProofGenerationContext` and `AnalyzedChatHistory`.
 * Generated proofs are represented by `GeneratedProofImpl` class and
 * can be further regenerated (fixed / shortened / etc), also keeping their previous versions.
 *
 * 1. All model parameters of the `ResolvedModelParams` type accepted by `LLMService`-related methods
 * are expected to be resolved by `resolveParameters` method beforehand.
 * This method resolves partially-undefined `InputModelParams` to complete and validated `ResolvedModelParams`.
 * See the `resolveParameters` method for more details.
 *
 * 2. All proofs-generation methods support errors handling and logging.
 *    - Each successfull generation is logged both by `GenerationsLogger` and `EventLogger`.
 *    - If error occurs, it is catched and then:
 *        - is wrapped into `LLMServiceError` and then...
 *        - in case of `LOG_EVENTS_AND_SWALLOW_ERRORS`, it's only logged by `EventLogger`;
 *        - in case of `RETHROW_ERRORS`, it's rethrown.
 *
 *    `EventLogger` sends `requestSucceededEvent` and `requestFailedEvent`
 *    (along with `LLMServiceRequest` as data), which can be handled then, for example, by the UI.
 *
 *     Regardless errors handling modes and `EventLogger` behaviour,
 *     `GenerationsLogger` maintains the logs of both successful and failed generations
 *     used for the further estimation of the service availability. See the `estimateTimeToBecomeAvailable` method.
 *
 * 3. To implement a new `LLMServiceImpl` based on generating proofs from chats, one should:
 *    - declare the specification of models parameters via custom `UserModelParams` and `ModelParams` interfaces;
 *    - implement custom `ParamsResolver` class, declaring the algorithm to resolve parameters with;
 *    - declare custom `GeneratedProofImpl`;
 *    - implement custom `LLMServiceInternal`;
 *    - finally, declare custom `LLMServiceImpl`.
 *
 *    I.e. `LLMServiceInternal` is effectively the only class needed to be actually implemented.
 *
 *    If proofs-generation is not supposed to be based on chats,
 *    the methods of `LLMServiceImpl` should be overriden directly too.
 *
 *    Also, do not be afraid of the complicated generic types in the base classes below.
 *    Although they look overly complex, they provide great typing support during implementation.
 *    Just remember to replace all generic types with your specific custom classes whenever possible.
 */
export abstract class LLMServiceImpl<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    LLMServiceInternalType extends LLMServiceInternal<ResolvedModelParams>,
> {
    protected abstract readonly internal: LLMServiceInternalType;
    protected abstract readonly modelParamsResolver: ParamsResolver<
        InputModelParams,
        ResolvedModelParams
    >;
    protected readonly eventLoggerGetter: () => EventLogger | undefined;
    protected readonly generationsLoggerBuilder: () => GenerationsLogger;

    /**
     * Creates an instance of `LLMServiceImpl`.
     * @param eventLogger if it is not specified, events won't be logged and passing `LOG_EVENTS_AND_SWALLOW_ERRORS` will throw an error.
     * @param debugLogs enables debug logs for the internal `GenerationsLogger`.
     * @param generationLogsFilePath if it is not specified, a temporary file will be used.
     */
    constructor(
        readonly serviceName: string,
        eventLogger: EventLogger | undefined,
        debugLogs: boolean,
        generationLogsFilePath: string | undefined
    ) {
        this.eventLoggerGetter = () => eventLogger;
        this.generationsLoggerBuilder = () =>
            new GenerationsLogger(
                generationLogsFilePath ?? tmp.fileSync().name,
                debugLogs
            );
    }

    static readonly requestSucceededEvent = `llmservice-request-succeeded`;
    static readonly requestFailedEvent = `llmservice-request-failed`;

    /**
     * Generates proofs from chat.
     * This method performs errors-handling and logging, check `LLMServiceImpl` docs for more details.
     *
     * The default implementation is based on the `LLMServiceInternal.generateFromChatImpl`.
     * If it is not the desired way, `generateFromChat` should be overriden.
     *
     * @param choices if specified, overrides `ModelParams.defaultChoices`.
     * @returns generated proofs as raw strings.
     */
    async generateFromChat(
        analyzedChat: AnalyzedChatHistory,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<string[]> {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            errorsHandlingMode,
            () => analyzedChat,
            (proof) => proof
        );
    }

    /**
     * Generates proofs from `ProofGenerationContext`, i.e. from `completionTarget` and `contextTheorems`.
     * This method performs errors-handling and logging, check `LLMServiceImpl` docs for more details.
     *
     * The default implementation is based on the generation from chat, namely,
     * it calls `LLMServiceInternal.generateFromChatImpl`.
     * If it is not the desired way, `generateProof` should be overriden.
     *
     * @param choices if specified, overrides `ModelParams.defaultChoices`.
     * @returns generated proofs as `GeneratedProofImpl`-s.
     */
    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<
        GeneratedProofImpl<ResolvedModelParams, LLMServiceInternalType>[]
    > {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            errorsHandlingMode,
            () => buildProofGenerationChat(proofGenerationContext, params),
            (proof) =>
                this.internal.constructGeneratedProof(
                    proof,
                    proofGenerationContext,
                    params
                ) as GeneratedProofImpl<
                    ResolvedModelParams,
                    LLMServiceInternalType
                >
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
     * Resolution process includes overrides of input parameters,
     * their resolution with default values if needed, and validation of their result values.
     * See the `ParamsResolver` class for more details.
     *
     * This method does not throw. Instead, it always returns resolution logs, which include
     * all information about the actions taken on the input parameters and their validation status.
     *
     * @param params possibly-incomplete parameters configured by user.
     * @returns complete and validated parameters for the further generation pipeline.
     */
    resolveParameters(
        params: InputModelParams
    ): ParamsResolutionResult<ResolvedModelParams> {
        return this.modelParamsResolver.resolve(params);
    }
}

/**
 * Facade type for the `GeneratedProofImpl<ResolvedModelParams>` type.
 *
 * Most often, proper typing of `GeneratedProofImpl.modelParams` is not required;
 * thus, outside of the internal implementation, this class will most likely be parameterized with `any`.
 */
export type GeneratedProof = GeneratedProofImpl<any, any>;

/**
 * This class represents a proof generated by `LLMServiceImpl`.
 * It stores all the meta information of its generation.
 *
 * Moreover, it might support multiround generation: fixing, shortening, etc.
 * For this, a new version of this proof could be generated via `LLMServiceInternal.generateFromChat`.
 *
 * Multiround-generation parameters are specified at `ModelParams.multiroundProfile`.
 *
 * Same to `LLMServiceImpl`, multiround-generation methods perform errors handling and logging (in the same way).
 * Same to `LLMServiceImpl`, these methods could be overriden to change the behaviour (of the multiround generation).
 *
 * Finally, `GeneratedProofImpl` keeps the previous proof versions (but not the future ones).
 */
export abstract class GeneratedProofImpl<
    ResolvedModelParams extends ModelParams,
    LLMServiceInternalType extends LLMServiceInternal<ResolvedModelParams>,
> {
    /**
     * An accessor for `ModelParams.multiroundProfile.maxRoundsNumber`.
     */
    readonly maxRoundsNumber: number;

    /**
     * Previous proof versions of the current `GeneratedProofImpl` (including the latest one).
     * Only the last one (i.e. the latest) is allowed to have an incomplete `ProofVersion`.
     *
     * When this `GeneratedProofImpl` is generated in a new round (for example, `fixProof` is called),
     * the `proofVersions` won't track the results (newer proof versions).
     * Completely new `GeneratedProofImpl` objects will be returned,
     * having longer `proofVersions` stored inside.
     */
    readonly proofVersions: ProofVersion[];

    /**
     * Creates an instance of `GeneratedProofImpl`.
     * Should be called only by `LLMServiceImpl`, `LLMServiceInternal` or `GeneratedProofImpl` itself.
     */
    constructor(
        proof: string,
        readonly proofGenerationContext: ProofGenerationContext,
        readonly modelParams: ResolvedModelParams,
        protected readonly llmServiceInternal: LLMServiceInternalType,
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
            throw Error(
                `proof cannot be instantiated: max rounds number (${this.maxRoundsNumber}) was already reached`
            );
        }
    }

    /**
     * @returns proof of the latest version for this `GeneratedProofImpl`.
     */
    proof(): string {
        return this.lastProofVersion().proof;
    }

    protected lastProofVersion(): ProofVersion {
        return this.proofVersions[this.proofVersions.length - 1];
    }

    /**
     * Initially generated proofs have version number equal to 1.
     * Each generation round creates `GeneratedProofs` with version = `this.versionNumber() + 1`.
     *
     * @returns version number of this `GeneratedProofImpl`.
     */
    versionNumber(): number {
        return this.proofVersions.length;
    }

    /**
     * This method doesn't check `ModelParams.multiroundProfile.fixedProofChoices`,
     * because they can be overriden via the function's parameters at the call.
     *
     * @returns whether this `GeneratedProofImpl` is allowed to be fixed at least once.
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
     * Generates new `GeneratedProofImpl`-s as fixes for the latest version of the current one.
     * This method performs errors-handling and logging the same way as `LLMServiceImpl`'s methods do.
     *
     * When this method is called, the `diagnostic` of the latest proof version
     * is overwritten with the `diagnostic` parameter of the call.
     *
     * The default implementation is based on the generation from chat, namely,
     * it calls `LLMServiceInternal.generateFromChatImpl`.
     * If it is not the desired way, `fixProof` should be overriden.
     *
     * @param diagnostic diagnostic received from the compiler.
     * @param choices if specified, overrides `ModelParams.multiroundProfile.defaultProofFixChoices`.
     */
    async fixProof(
        diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<
        GeneratedProofImpl<ResolvedModelParams, LLMServiceInternalType>[]
    > {
        return this.llmServiceInternal.generateFromChatWrapped(
            this.modelParams,
            choices,
            errorsHandlingMode,
            () => {
                if (!this.canBeFixed()) {
                    throw new ConfigurationError(
                        `this \`GeneratedProofImpl\` could not be fixed: version ${this.versionNumber()} >= max rounds number ${this.maxRoundsNumber}`
                    );
                }
                this.lastProofVersion().diagnostic = diagnostic;
                return buildProofFixChat(
                    this.proofGenerationContext,
                    this.proofVersions,
                    this.modelParams
                );
            },
            (proof: string) =>
                this.llmServiceInternal.constructGeneratedProof(
                    this.removeProofQedIfNeeded(proof),
                    this.proofGenerationContext,
                    this.modelParams,
                    this.proofVersions
                ) as GeneratedProofImpl<
                    ResolvedModelParams,
                    LLMServiceInternalType
                >
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
> {
    readonly eventLogger: EventLogger | undefined;
    readonly generationsLogger: GenerationsLogger;
    readonly debug: DebugWrappers;

    constructor(
        readonly llmService: LLMServiceImpl<
            any,
            ResolvedModelParams,
            LLMServiceInternal<ResolvedModelParams>
        >,
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
    ): GeneratedProofImpl<
        ResolvedModelParams,
        LLMServiceInternal<ResolvedModelParams>
    >;

    /**
     * This method should be mostly a pure implementation of
     * the generation from chat, namely, its happy path.
     * This function doesn't need to handle errors!
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
     * Subnote: most likely you'd like to call `this.validateChoices` to validate `choices` parameter.
     * Since it overrides `choices`-like parameters of already validated `params`, it might have any number value.
     */
    abstract generateFromChatImpl(
        chat: ChatHistory,
        params: ResolvedModelParams,
        choices: number
    ): Promise<string[]>;

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
        wrapRawProof: (proof: string) => T
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
                    request.analyzedChat!.chat,
                    params,
                    choices
                );
            },
            wrapRawProof
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
        generateProofs: (request: LLMServiceRequest) => Promise<string[]>,
        wrapRawProof: (proof: string) => T
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
            const proofs = await generateProofs(request);
            this.logSuccess(request, proofs);
            return proofs.map(wrapRawProof);
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
    validateChoices(choices: number) {
        if (choices <= 0) {
            throw new ConfigurationError("choices number should be positive");
        }
    }

    private logSuccess(
        request: LLMServiceRequest,
        generatedRawProofs: string[]
    ) {
        const requestSucceeded: LLMServiceRequestSucceeded = {
            ...request,
            generatedRawProofs: generatedRawProofs,
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
