import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ProofProviderControlParams } from "../../../proofProviders/impl/utils/proofProviderControlParams";
import { ProofProviderSerializer } from "../../../proofProviders/impl/utils/serialization/proofProviderSerializer";
import { toOneLineLogString } from "../../../proofProviders/impl/utils/serialization/toLog";

import { unsupported } from "../../../utils/errors/throwErrors";

import { BenchTestService } from "./benchTestService";
import { ResolvedBenchTestServiceParams } from "./benchTestServiceParams";

export class BenchTestServiceSerializer extends ProofProviderSerializer {
    protected selfClass = BenchTestServiceSerializer;

    static readonly serializationType = "benchTest";
    static {
        ProofProviderSerializer.registerSelfSerialization(
            this.serializationType,
            BenchTestServiceSerializer
        );
    }

    static readonly shortName = "Benchmarking Test";

    constructor(
        private readonly resolvedServiceParams: ResolvedBenchTestServiceParams
    ) {
        super();
    }

    constructProofProvider(
        controlParams: ProofProviderControlParams
    ): ProofProvider {
        return new BenchTestService({
            ...this.resolvedServiceParams,
            ...controlParams,
        });
    }

    toLogString(verbose: boolean): string {
        return toOneLineLogString(
            BenchTestServiceSerializer.shortName,
            this.resolvedServiceParams,
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
