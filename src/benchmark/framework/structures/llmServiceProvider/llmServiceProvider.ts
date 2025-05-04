import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { ParamsResolverImpl } from "../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../llm/userModelParams";

import { EventLogger } from "../../../../logging/eventLogger";
import { AsyncScheduler } from "../../../../utils/async/asyncScheduler";
import {
    invariantFailed,
    throwError,
} from "../../../../utils/errors/throwErrors";

import { InstallerProvider } from "./installerProvider";

export abstract class LLMServiceProvider {
    protected abstract readonly selfClass: LLMServiceProviderClass;

    /**
     * Unique string to identify this provider during deserialization.
     *
     * **_Important:_** Implementation class **must** define this property its own way
     * and register it via `registerSelfSerialization(...)` call in the `static` block.
     */
    static readonly serializationType: string;

    getSerializationType(): string {
        return this.selfClass.serializationType;
    }

    protected static registerSelfSerialization(
        serializationType: string,
        self: LLMServiceProviderClass
    ) {
        if (this.serializationTypeToClass.has(serializationType)) {
            invariantFailed(
                "`LLMServiceProvider`",
                "each `serializationType` can be registered only once, ",
                `failed to register "${serializationType}"`
            );
        }
        this.serializationTypeToClass.set(serializationType, self);
    }

    /**
     * _Note:_ provided `eventLogger` and `errorsHandlingMode` **must** be used
     * to construct the resulting `LLMService`;
     * otherwise, internal invariants of the framework might be violated.
     */
    abstract constructService(
        eventLogger: EventLogger | undefined,
        errorsHandlingMode: ErrorsHandlingMode
    ): LLMService<UserModelParams, ModelParams>;

    /**
     * Return `undefined` if no installation is needed.
     */
    abstract getInstallerProvider(): InstallerProvider | undefined;

    abstract getParamsResolver(): ParamsResolverImpl<
        UserModelParams,
        ModelParams
    >;

    /**
     * Select a scheduler to execute the `modelParams` model.
     * This method allows to control the maximum parallelism for services' models.
     *
     * Check `SchedulersProvider` and its implementations for more insights.
     */
    abstract selectScheduler(modelParams: ModelParams): AsyncScheduler;

    /**
     * Pretty output to show in logs.
     */
    abstract toLogString(verbose: boolean): string;

    /**
     * It is important to implement this method compatible with the static `deserialize(...)`
     * to support proper recovery from disk. If it is impossible to do, **do not throw an exception** here,
     * it might halt the successful benchmarks execution
     * (the framework might try to save the input for the future recovery).
     */
    abstract serializeData(): any;

    static deserealizeBy(
        serializationType: string,
        serializedProviderData: any
    ): LLMServiceProvider {
        const serviceProviderClass =
            this.serializationTypeToClass.get(serializationType) ??
            throwError(
                "`LLMServiceProvider` deserialization failed: ",
                `uknown serialization type "${serializationType}"`
            );
        return serviceProviderClass.deserialize(serializedProviderData);
    }

    private static readonly serializationTypeToClass: Map<
        string,
        LLMServiceProviderClass
    > = new Map();
}

export interface LLMServiceProviderClass {
    new (...args: any[]): LLMServiceProvider;

    /**
     * Unique string to identify this provider during deserialization.
     *
     * **_Important:_** Implementation class **must** define this property its own way
     * and register it via `registerSelfSerialization(...)` call.
     */
    readonly serializationType: string;

    /**
     * Recreate an instance of this provider from serialized data.
     *
     * _Implementation note:_ Throw an exeption here if serialization-deserialization cycle is not fully possible
     * for the implemented service provider. This way, it will state that such service provider
     * does not support recovery from disk.
     */
    deserialize(serializedProviderData: any): LLMServiceProvider;
}
