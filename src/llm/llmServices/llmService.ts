import * as tmp from "tmp";

import { EventLogger } from "../../logging/eventLogger";
import { ConfigurationError, LLMServiceError } from "../llmServiceErrors";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory } from "./chat";
import { LLMServiceInternal } from "./llmServiceInternal";
import { ModelParams } from "./modelParams";
import {
    buildProofFixChat,
    buildProofGenerationChat,
} from "./utils/chatFactory";
import { estimateTimeToBecomeAvailableDefault } from "./utils/defaultAvailabilityEstimator";
import { GenerationsLogger } from "./utils/generationsLogger/generationsLogger";
import { LoggerRecord } from "./utils/generationsLogger/loggerRecord";
import {
    ParamsResolutionResult,
    ParamsResolver,
} from "./utils/paramsResolvers/abstractResolvers";
import { Time } from "./utils/time";

export interface ProofVersion {
    proof: string;
    diagnostic?: string;
}

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
    llmService: LLMService<UserModelParams, ModelParams>;
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
 * Facade type for the `LLMServiceImpl<InputModelParams, ResolvedModelParams, LLMServiceType, GeneratedProofType, LLMServiceInternalType>` type.
 *
 * The proper typing of self `LLMServiceImpl`, returning `GeneratedProofImpl`-s and `LLMServiceImpl.internal`
 * is required inside implementation only.
 * Thus, `LLMServiceImpl` should be resolved with `any` for the implementation generic types, when used outside.
 */
export type LLMService<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
> = LLMServiceImpl<InputModelParams, ResolvedModelParams, any, any, any>;

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
 *    For example:
 *    ```
 *    class MyLLMService extends LLMServiceImpl<
 *        MyUserModelParams,
 *        MyModelParams,
 *        MyLLMService,
 *        MyGeneratedProof,
 *        MyLLMServiceInternal
 *    > {
 *        // implementation
 *    }
 *    ```
 */
export abstract class LLMServiceImpl<
    InputModelParams extends UserModelParams,
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
                {
                    debug: debugLogs,
                    paramsPropertiesToCensor: {
                        apiKey: GenerationsLogger.censorString,
                    },
                    cleanLogsOnStart: true,
                }
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
    ): Promise<GeneratedProofType[]> {
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
                )
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
 * Facade type for the `GeneratedProofImpl<ResolvedModelParams, GeneratedProofType, LLMServiceInternalType>` type.
 *
 * Most often, the proper typing of `GeneratedProofImpl.modelParams` is not required,
 * while the proper typing of the parent `LLMServiceImpl`, returning `GeneratedProofImpl`-s and `GeneratedProofImpl.llmServiceInternal`
 * is required inside implementation only.
 * Thus, outside of the internal implementation, this class will most likely be parameterized with base classes and any-s.
 */
export type GeneratedProof = GeneratedProofImpl<
    ModelParams,
    LLMService<UserModelParams, ModelParams>,
    GeneratedProof,
    any
>;

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
     *
     * This constructor is capable of extracting the actual proof (its block of code)
     * from the input `proof` in case it is contaminated with plain text or any other surrounding symbols.
     * Namely, it extracts the block between `Proof.` and `Qed.` if they are present;
     * otherwise, takes the whole `proof`.
     */
    constructor(
        proof: string,
        readonly proofGenerationContext: ProofGenerationContext,
        readonly modelParams: ResolvedModelParams,
        protected readonly llmServiceInternal: LLMServiceInternalType,
        previousProofVersions: ProofVersion[] = []
    ) {
        // Make a copy of the previous proof versions
        this.proofVersions = [...previousProofVersions];

        // Save newly generated `proof`
        this.proofVersions.push({
            proof: this.removeProofQedIfNeeded(proof),
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
    ): Promise<GeneratedProofType[]> {
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
                    proof,
                    this.proofGenerationContext,
                    this.modelParams,
                    this.proofVersions
                )
        );
    }

    private readonly coqProofBlockPattern = /Proof\.\s*(.*?)\s*Qed\./s;

    private removeProofQedIfNeeded(message: string): string {
        const match = this.coqProofBlockPattern.exec(message);
        if (match) {
            return match[1];
        } else {
            return message;
        }
    }
}
