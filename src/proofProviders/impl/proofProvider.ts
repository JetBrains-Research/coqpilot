import { MessageHandler } from "../../utils/structures/messageHandler";
import { Time } from "../../utils/time";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory } from "./commonStructures/chat";
import { InstallerProvider } from "./commonStructures/installerProvider";
import { ProofGenerationMetadataHolder } from "./commonStructures/proofGenerationMetadata";
import { GeneratedProof } from "./generatedProof";
import { ModelParams } from "./modelParams";
import { ProofProviderIdentifier } from "./proofProviderIdentifier";
import { ProofProviderInternal } from "./proofProviderInternal";
import {
    ProofProviderParams,
    ResolvedProofProviderParams,
    resolveProofProviderParamsWithDefaults,
} from "./proofProviderParams";
import { buildProofGenerationChat } from "./utils/chatFactory";
import { estimateTimeToBecomeAvailableDefault } from "./utils/defaultAvailabilityEstimator";
import { LoggerRecord } from "./utils/generationsLogger/loggerRecord";
import {
    ParamsResolutionResult,
    ParamsResolver,
} from "./utils/paramsResolvers/abstractResolvers";
import { ProofProviderSerializer } from "./utils/serialization/proofProviderSerializer";
import { SerializedProofProvider } from "./utils/serialization/serializedProofProvider";

/**
 * `ProofProvider` represents a proofProvider for proofs generation.
 * Proofs can be generated from both `ProofGenerationContext` and `AnalyzedChatHistory`.
 * Generated proofs are represented by `GeneratedProof` class and
 * can be further regenerated (fixed / shortened / etc), also keeping their previous versions.
 *
 *
 * 1. All model parameters of the `ResolvedModelParams` type accepted by `ProofProvider`-related methods
 *    are expected to be resolved by `resolveParameters` method beforehand.
 *    This method resolves partially-undefined `InputModelParams` to complete and validated `ResolvedModelParams`.
 *    See the `resolveParameters` method for more details.
 *
 * 2. All proofs-generation methods support errors handling and logging.
 *    - Each successfull generation is logged both by `GenerationsLogger` and `EventLogger`.
 *    - If error occurs, it is catched and then:
 *        - is wrapped into `ProofProviderError` and then...
 *        - in case of `LOG_EVENTS_AND_SWALLOW_ERRORS`, it's only logged by `EventLogger`;
 *        - in case of `RETHROW_ERRORS`, it's rethrown.
 *
 *    `EventLogger` sends `requestSucceededEvent` and `requestFailedEvent`
 *    (along with `ProofProviderRequest` as data), which can be handled then, for example, by the UI.
 *
 *     Regardless errors handling modes and `EventLogger` behaviour,
 *     `GenerationsLogger` maintains the logs of both successful and failed generations
 *     used for the further estimation of the proofProvider availability. See the `estimateTimeToBecomeAvailable` method.
 *
 * 3. `ProofProvider` is responsible for the way to interact with the actual proof-generation proofProvider,
 *    meaning all proof-generation requests to the actual proofProvider should be scheduled
 *    through the same `ProofProvider` instance.
 *    Thus, only one instance of each `ProofProvider` type is maintained active by default.
 *    However, there can be exceptions, see `ProofProvider.isSameInstance(...)` for more details.
 *
 * 4. To implement a new `ProofProvider` based on generating proofs from chats, one should:
 *    - declare the specification of models parameters via custom `UserModelParams` and `ModelParams` interfaces;
 *    - implement custom `ParamsResolver` class, declaring the algorithm to resolve parameters with;
 *    - declare custom `GeneratedProof`;
 *    - implement custom `ProofProviderInternal`;
 *    - finally, declare custom `ProofProvider`.
 *
 *    I.e. `ProofProviderInternal` is effectively the only class needed to be actually implemented.
 *
 *    If proofs-generation is not supposed to be based on chats,
 *    the methods of `ProofProvider` should be overriden directly too.
 *
 *    Also, do not be afraid of the complicated generic types in the base classes below.
 *    Although they look overly complex, they provide great typing support during implementation.
 *    Just remember to replace all generic types with your specific custom classes whenever possible.
 *    For example:
 *    ```
 *    class MyProofProvider extends ProofProvider<
 *        MyUserModelParams,
 *        MyModelParams,
 *        MyProofProvider,
 *        MyGeneratedProof,
 *        MyProofProviderInternal
 *    > {
 *        // implementation
 *    }
 *    ```
 */
export abstract class ProofProvider<
    InputModelParams extends UserModelParams = UserModelParams,
    ResolvedModelParams extends ModelParams = ModelParams,
    ProofProviderType extends ProofProvider<
        UserModelParams,
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
    GeneratedProofType extends GeneratedProof<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
    ProofProviderInternalType extends ProofProviderInternal<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
> {
    abstract readonly name: string;
    abstract readonly identifier: ProofProviderIdentifier | undefined;

    protected abstract readonly internal: ProofProviderInternalType;
    protected abstract readonly modelParamsResolver: ParamsResolver<
        InputModelParams,
        ResolvedModelParams
    >;
    /**
     * Provides serialization-deserialization cycle for the given `ProofProvider`.
     *
     * Check implementations of `ProofProviderSerializer` for more insights
     * (for example, `BasicProofProviderSerializer` via `provideBasicSerializer(...)`).
     */
    protected abstract readonly serializer: ProofProviderSerializer;

    // TODO: parametrize class with `ResolvedProofProviderParams`,
    // so as to support custom ones better
    readonly proofProviderSetup: ResolvedProofProviderParams;

    /**
     * Creates an instance of `ProofProvider`.
     */
    constructor(proofProviderParams: ProofProviderParams = {}) {
        this.proofProviderSetup =
            resolveProofProviderParamsWithDefaults(proofProviderParams);
    }

    static readonly requestSucceededEvent = `proof-provider-request-succeeded`;
    static readonly requestFailedEvent = `proof-provider-request-failed`;

    /**
     * Generates proofs based on chat input.
     * This method performs errors-handling and logging, check `ProofProvider` docs for more details.
     *
     * The default implementation relies on `ProofProviderInternal.generateFromChatImpl`.
     * If a different behavior is required, the `generateFromChat` method should be overridden;
     * however, maintaining all errors-handling and logging invariants and, perfectly, models scheduling.
     * Consider `ProofProviderInternal.scheduleLoggedGenerationAndHandleErrors` for help.
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
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        abortSignal?: AbortSignal,
        onSchedulerDebugLog: MessageHandler = this.internal
            .sendDebugEventOnSchedulerLog
    ): Promise<string[]> {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            metadataHolder,
            abortSignal,
            onSchedulerDebugLog,
            () => analyzedChat,
            (rawProof) => rawProof.content
        );
    }

    /**
     * Generates proofs from `ProofGenerationContext`, i.e. from `completionTarget` and `contextTheorems`.
     * This method performs errors-handling and logging, check `ProofProvider` docs for more details.
     *
     * The default implementation is based on the generation from chat, namely,
     * it calls `ProofProviderInternal.generateFromChatImpl`.
     * If it is not the desired way, `generateProof` should be overriden;
     * however, maintaining all errors-handling and logging invariants and, perfectly, models scheduling.
     * Consider `ProofProviderInternal.scheduleLoggedGenerationAndHandleErrors` for help.
     *
     * @param proofGenerationContext the context used as input for proof generation.
     * @param params resolved model parameters for configuring the generation process.
     * @param choices specifies the number of choices for generation. If not provided, the `params.defaultChoices` value is used.
     * @param metadataHolder if provided, stores metadata about the proof generation process, which can be analyzed later.
     * @returns an array of generated proofs as `GeneratedProof`-s.
     */
    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        abortSignal?: AbortSignal,
        onSchedulerDebugLog: MessageHandler = this.internal
            .sendDebugEventOnSchedulerLog
    ): Promise<GeneratedProofType[]> {
        return this.internal.generateFromChatWrapped(
            params,
            choices,
            metadataHolder,
            abortSignal,
            onSchedulerDebugLog,
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
     * Provide installer with its options to perform required installations with
     * for this `ProofProvider` to functionate.
     *
     * By default, this function returns `undefined`, meaning no installation is needed.
     *
     * For its implementation for an external proofProvider check
     * `AbstractExternalProofProvider` and `AbstractProofProviderInstaller`.
     */
    readonly installerProvider: InstallerProvider | undefined = undefined;

    /**
     * Estimates the expected time for proofProvider to become available.
     * To do this, analyzes the logs from `this.generationsLogger` and computes the time.
     */
    estimateTimeToBecomeAvailable(): Time {
        return estimateTimeToBecomeAvailableDefault(
            this.internal.generationsLogger.readLogsSinceLastSuccess()
        );
    }

    /**
     * Reads logs provided by `GenerationsLogger` for this proofProvider.
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

    /**
     * Serialize `ProofProvider` to disk via defined `this.serializer`.
     *
     * This method never throws, so as not to halt a successful execution.
     * If recovery from the disk is impossible, deserialization should throw.
     */
    readonly serialize = (): SerializedProofProvider => {
        return this.serializer.serialize();
    };

    readonly toLogString = (verbose: boolean): string => {
        return this.serializer.toLogString(verbose);
    };

    /**
     * This function controls the rule to maintain instances of this `ProofProvider`.
     * Only instances that marked as different (so that `isSameInstance` return `false`)
     * can coexist together. Otherwise, an error will be thrown on attempt to register the second instance
     * (see `ProofProvidersStorage` for more details).
     *
     * Basically, this function prevents from accident creation of different instances of the same proofProvider,
     * so that no more global control to the actual proofProvider is possible (different instances will use
     * different models schedulers, for example).
     *
     * However, sometimes this function might return `false`: for example, the same external proofProvider
     * might be instantiated with different installation paths, so basically such instances will correspond
     * to different actual proofProviders.
     *
     * *_All in all, implementation note:_* return `true` by default, so to force having only
     * one instance of `ProofProvider` per execution. Return `false` if you want to provide more flexibility,
     * but do it carefully checking the setup.
     */
    isSameInstance(_other: ProofProvider): boolean {
        return true;
    }
}
