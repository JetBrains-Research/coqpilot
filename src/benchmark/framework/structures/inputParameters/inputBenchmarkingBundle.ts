import { DatasetInputTargets } from "../common/inputTargets";
import { LLMServiceIdentifier } from "../common/llmServiceIdentifier";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export type InputBenchmarkingBundle =
    InputBenchmarkingBundleImpl<InputBenchmarkingModelParams.Params>;

export interface InputBenchmarkingBundleImpl<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    requestedTargets: DatasetInputTargets;
}
