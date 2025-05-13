import { LLMService } from "../../../llm/llmServices/llmService";
import { LLMServiceControlParams } from "../../../llm/llmServices/utils/llmServiceControlParams";
import { LLMServiceSerializer } from "../../../llm/llmServices/utils/serialization/llmServiceSerializer";
import { toOneLineLogString } from "../../../llm/llmServices/utils/serialization/toLog";

import { unsupported } from "../../../utils/errors/throwErrors";

import { BenchTestService } from "./benchTestService";
import { ResolvedBenchTestServiceParams } from "./benchTestServiceParams";

export class BenchTestServiceSerializer extends LLMServiceSerializer {
    protected selfClass = BenchTestServiceSerializer;

    static readonly serializationType = "benchTest";
    static {
        LLMServiceSerializer.registerSelfSerialization(
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

    constructService(controlParams: LLMServiceControlParams): LLMService {
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

    static deserialize(_serializedProviderData: any): LLMServiceSerializer {
        unsupported(
            "Deserialization of `BenchTestService` is currently unsupported"
        );
    }
}
