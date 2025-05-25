import { buildErrorCompleteLog } from "../../../../utils/errors/errorsUtils";
import {
    invariantFailed,
    throwError,
    unreachable,
} from "../../../../utils/errors/throwErrors";
import { ProofProvider } from "../../proofProvider";
import { ProofProviderConstructor } from "../../proofProviderConstructor";
import { ProofProviderControlParams } from "../proofProviderControlParams";

import { SerializedProofProvider } from "./serializedProofProvider";

export abstract class ProofProviderSerializer {
    protected abstract readonly selfClass: ProofProviderSerializerClass;

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
        self: ProofProviderSerializerClass
    ) {
        if (this.serializationTypeToClass.has(serializationType)) {
            invariantFailed(
                "`ProofProviderSerializer`",
                "each `serializationType` can be registered only once, ",
                `failed to register "${serializationType}"`
            );
        }
        this.serializationTypeToClass.set(serializationType, self);
    }

    /**
     * _Note:_ provided `controlParams` **must** be used to construct the resulting `ProofProvider`;
     * otherwise, internal invariants of the framework might be violated.
     */
    abstract constructProofProvider(
        controlParams: ProofProviderControlParams
    ): ProofProvider;

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

    readonly serialize = (): SerializedProofProvider => {
        try {
            return {
                serializationType: this.getSerializationType(),
                serializedData: this.serializeData(),
            };
        } catch (e) {
            unreachable(
                "`ProofProviderSerializer.serialize()` should never throw, ",
                `but an error occurred: ${buildErrorCompleteLog(e)}`
            );
        }
    };

    static deserealizeBy(
        serializationType: string,
        serializedProviderData: any
    ): ProofProviderConstructor {
        const serializerClass =
            this.serializationTypeToClass.get(serializationType) ??
            throwError(
                "`ProofProviderSerializer` deserialization failed: ",
                `uknown serialization type "${serializationType}"`
            );
        return serializerClass.deserialize(serializedProviderData)
            .constructProofProvider;
    }

    private static readonly serializationTypeToClass: Map<
        string,
        ProofProviderSerializerClass
    > = new Map();
}

export interface ProofProviderSerializerClass {
    new (...args: any[]): ProofProviderSerializer;

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
     * for the implemented proofProvider provider. This way, it will state that such proofProvider provider
     * does not support recovery from disk.
     */
    deserialize(serializedProviderData: any): ProofProviderSerializer;
}
