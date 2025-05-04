import { DatasetInputTargets } from "../common/inputTargets";
import { LLMServiceProvider } from "../llmServiceProvider/llmServiceProvider";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export type InputBenchmarkingBundle =
    InputBenchmarkingBundleImpl<InputBenchmarkingModelParams.Params>;

export interface InputBenchmarkingBundleImpl<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceProvider: LLMServiceProvider;
    inputBenchmarkingModelsParams: InputParams[];
    requestedTargets: DatasetInputTargets;
}
