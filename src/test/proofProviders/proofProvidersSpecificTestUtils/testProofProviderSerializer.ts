import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderControlParams } from "../../../proofProviders/impl/utils/proofProviderControlParams";
import { ProofProviderSerializer } from "../../../proofProviders/impl/utils/serialization/proofProviderSerializer";
import { toOneLineLogString } from "../../../proofProviders/impl/utils/serialization/toLog";

import { unsupported } from "../../../utils/errors/throwErrors";

export function provideTestSerializer<T>(
    data: T,
    constructTestService: (
        data: T,
        controlParams: ProofProviderControlParams
    ) => ProofProvider
): TestServiceSerializer<T> {
    return new TestServiceSerializer(data, constructTestService);
}

export class TestServiceSerializer<T> extends ProofProviderSerializer {
    protected selfClass = TestServiceSerializer;

    static readonly serializationType = "test";
    static {
        ProofProviderSerializer.registerSelfSerialization(
            this.serializationType,
            TestServiceSerializer
        );
    }

    static readonly shortName = "Test";

    constructor(
        private readonly data: T,
        private readonly constructTestService: (
            data: T,
            controlParams: ProofProviderControlParams
        ) => ProofProvider
    ) {
        super();
    }

    constructProofProvider(
        controlParams: ProofProviderControlParams
    ): ProofProvider {
        return this.constructTestService(this.data, controlParams);
    }

    toLogString(verbose: boolean): string {
        return toOneLineLogString(
            TestServiceSerializer.shortName,
            this.data,
            verbose
        );
    }

    serializeData(): {} {
        return {};
    }

    static deserialize(_serializedProviderData: any): ProofProviderSerializer {
        unsupported(
            "Deserialization of `BenchTestService` is currently unsupported"
        );
    }
}
