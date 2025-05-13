import { LLMService } from "../../../llm/llmServices/llmService";
import { LLMServiceControlParams } from "../../../llm/llmServices/utils/llmServiceControlParams";
import { LLMServiceSerializer } from "../../../llm/llmServices/utils/serialization/llmServiceSerializer";
import { toOneLineLogString } from "../../../llm/llmServices/utils/serialization/toLog";

import { unsupported } from "../../../utils/errors/throwErrors";

export function provideTestSerializer<T>(
    data: T,
    constructTestService: (
        data: T,
        controlParams: LLMServiceControlParams
    ) => LLMService
): TestServiceSerializer<T> {
    return new TestServiceSerializer(data, constructTestService);
}

export class TestServiceSerializer<T> extends LLMServiceSerializer {
    protected selfClass = TestServiceSerializer;

    static readonly serializationType = "test";
    static {
        LLMServiceSerializer.registerSelfSerialization(
            this.serializationType,
            TestServiceSerializer
        );
    }

    static readonly shortName = "Test";

    constructor(
        private readonly data: T,
        private readonly constructTestService: (
            data: T,
            controlParams: LLMServiceControlParams
        ) => LLMService
    ) {
        super();
    }

    constructService(controlParams: LLMServiceControlParams): LLMService {
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

    static deserialize(_serializedProviderData: any): LLMServiceSerializer {
        unsupported(
            "Deserialization of `BenchTestService` is currently unsupported"
        );
    }
}
