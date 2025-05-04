import { SerializedLLMServiceProvider } from "../../llmServiceProvider/llmServiceProviderSerialization";
import { InputBenchmarkingModelParams } from "../inputBenchmarkingModelParams";

export interface LightweightInputModelParams
    extends InputBenchmarkingModelParams.Params {
    llmServiceProvider: SerializedLLMServiceProvider;
}
