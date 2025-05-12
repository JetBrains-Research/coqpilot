import { SerializedLLMService } from "../../../../../llm/llmServices/utils/serialization/serializedLLMService";

import { InputBenchmarkingModelParams } from "../inputBenchmarkingModelParams";

export interface LightweightInputModelParams
    extends InputBenchmarkingModelParams.Params {
    serializedService: SerializedLLMService;
}
