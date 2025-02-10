import * as tmp from "tmp";

import { EventLogger } from "../../logging/eventLogger";
import { Time } from "../../utils/time";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory } from "./commonStructures/chat";
import { ErrorsHandlingMode } from "./commonStructures/errorsHandlingMode";
import { ProofGenerationMetadataHolder } from "./commonStructures/proofGenerationMetadata";
import { GeneratedProofImpl } from "./generatedProof";
import { LLMServiceInternal } from "./llmServiceInternal";
import { ModelParams } from "./modelParams";
import { buildProofGenerationChat } from "./utils/chatFactory";
import { estimateTimeToBecomeAvailableDefault } from "./utils/defaultAvailabilityEstimator";
import { GenerationsLogger } from "./utils/generationsLogger/generationsLogger";
import { LoggerRecord } from "./utils/generationsLogger/loggerRecord";
import {
    ParamsResolutionResult,
    ParamsResolver,
} from "./utils/paramsResolvers/abstractResolvers";

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
    abstract readonly serviceName: string;
    protected abstract readonly internal: LLMServiceInternalType;
    protected abstract readonly modelParamsResolver: ParamsResolver<
        InputModelParams,
        ResolvedModelParams
    >;

    protected readonly eventLogger: EventLogger | undefined;
    readonly errorsHandlingMode: ErrorsHandlingMode;
    readonly generationLogsFilePath: string;
    protected readonly generationsLoggerBuilder: () => GenerationsLogger;

    /**
     * Creates an instance of `LLMServiceImpl`.
     * @param eventLogger is used to send proof generation events. If not specified, event logging will be disabled.
     * @param errorsHandlingMode defines how errors during method calls are handled: whether they are rethrown or swallowed. Regardless of the mode, errors are logged.
     * @param debugLogs enables debug logs for the internal `GenerationsLogger`.
     * @param generationLogsFilePath if it is not specified, a temporary file will be used.
     */
    constructor(
        eventLogger: EventLogger | undefined = undefined,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.RETHROW_ERRORS,
        generationLogsFilePath: string | undefined = undefined,
        debugLogs: boolean = false
    ) {
        this.eventLogger = eventLogger;
        this.errorsHandlingMode = errorsHandlingMode;
        this.generationLogsFilePath =
            generationLogsFilePath ?? tmp.fileSync().name;
        this.generationsLoggerBuilder = () =>
            new GenerationsLogger(this.generationLogsFilePath, {
                debug: debugLogs,
                paramsPropertiesToCensor: {
                    apiKey: GenerationsLogger.censorString,
                },
                cleanLogsOnStart: true,
            });
    }

    static readonly requestSucceededEvent = `llmservice-request-succeeded`;
    static readonly requestFailedEvent = `llmservice-request-failed`;

    /**
     * Generates proofs based on chat input.
     * This method performs errors-handling and logging, check `LLMServiceImpl` docs for more details.
     *
     * The default implementation relies on `LLMServiceInternal.generateFromChatImpl`.
     * If a different behavior is required, the `generateFromChat` method should be overridden;
     * however, maintaining all errors-handling and logging invariants.
     * Consider `LLMServiceInternal.logGenerationAndHandleErrors` for help.
     *
     * @param analyzedChat the analyzed chat history used as input for proof generation.
     * @param params resolved model parameters for configuring the generation process.
     * @param choices specifies the number of choices for generation. If not provided, the `params.defaultChoices` value is used.
     * @param metadataHolder if provided, stores metadata about the proof generation process, which can be analyzed later.
     * @returns an array of generated proofs as raw strings.
     */
    async generateFromChat(
        analyzedChat: AnalyzedChatHistory,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined
    ): Promise<string[]> {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            metadataHolder,
            () => analyzedChat,
            (rawProof) => rawProof.content
        );
    }

    /**
     * Generates proofs from `ProofGenerationContext`, i.e. from `completionTarget` and `contextTheorems`.
     * This method performs errors-handling and logging, check `LLMServiceImpl` docs for more details.
     *
     * The default implementation is based on the generation from chat, namely,
     * it calls `LLMServiceInternal.generateFromChatImpl`.
     * If it is not the desired way, `generateProof` should be overriden;
     * however, maintaining all errors-handling and logging invariants.
     * Consider `LLMServiceInternal.logGenerationAndHandleErrors` for help.
     *
     * @param proofGenerationContext the context used as input for proof generation.
     * @param params resolved model parameters for configuring the generation process.
     * @param choices specifies the number of choices for generation. If not provided, the `params.defaultChoices` value is used.
     * @param metadataHolder if provided, stores metadata about the proof generation process, which can be analyzed later.
     * @returns an array of generated proofs as `GeneratedProofImpl`-s.
     */
    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined
    ): Promise<GeneratedProofType[]> {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            metadataHolder,
            () => buildProofGenerationChat(proofGenerationContext, params),
            (rawProof) =>
                this.internal.constructGeneratedProof(
                    rawProof,
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
