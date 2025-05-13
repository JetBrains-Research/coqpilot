import { buildErrorCompleteLog } from "../../../../utils/errors/errorsUtils";
import {
    invariantFailed,
    throwError,
    unreachable,
} from "../../../../utils/errors/throwErrors";
import { LLMService } from "../../llmService";
import { LLMServiceProvider } from "../../llmServiceProvider";
import { LLMServiceControlParams } from "../llmServiceControlParams";

import { SerializedLLMService } from "./serializedLLMService";

export abstract class LLMServiceSerializer {
    protected abstract readonly selfClass: LLMServiceSerializerClass;

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
        self: LLMServiceSerializerClass
    ) {
        if (this.serializationTypeToClass.has(serializationType)) {
            invariantFailed(
                "`LLMServiceSerializer`",
                "each `serializationType` can be registered only once, ",
                `failed to register "${serializationType}"`
            );
        }
        this.serializationTypeToClass.set(serializationType, self);
    }

    /**
     * _Note:_ provided `controlParams` **must** be used to construct the resulting `LLMService`;
     * otherwise, internal invariants of the framework might be violated.
     */
    abstract constructService(
        controlParams: LLMServiceControlParams
    ): LLMService;

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

    readonly serialize = (): SerializedLLMService => {
        try {
            return {
                serializationType: this.getSerializationType(),
                serializedData: this.serializeData(),
            };
        } catch (e) {
            unreachable(
                "`LLMServiceSerializer.serialize()` should never throw, ",
                `but an error occurred: ${buildErrorCompleteLog(e)}`
            );
        }
    };

    static deserealizeBy(
        serializationType: string,
        serializedProviderData: any
    ): LLMServiceProvider {
        const serializerClass =
            this.serializationTypeToClass.get(serializationType) ??
            throwError(
                "`LLMServiceSerializer` deserialization failed: ",
                `uknown serialization type "${serializationType}"`
            );
        return serializerClass.deserialize(serializedProviderData)
            .constructService;
    }

    private static readonly serializationTypeToClass: Map<
        string,
        LLMServiceSerializerClass
    > = new Map();
}

export interface LLMServiceSerializerClass {
    new (...args: any[]): LLMServiceSerializer;

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
    deserialize(serializedProviderData: any): LLMServiceSerializer;
}
