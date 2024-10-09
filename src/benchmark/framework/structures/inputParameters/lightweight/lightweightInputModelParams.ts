import { LLMServiceIdentifier } from "../../common/llmServiceIdentifier";
import { InputBenchmarkingModelParams } from "../inputBenchmarkingModelParams";

export interface LightweightInputModelParams
    extends InputBenchmarkingModelParams.Params {
    llmServiceIdentifier: LLMServiceIdentifier;
}
