import { InputBenchmarkingModelParams } from "../experiment/inputBenchmarkingModelParams";

import { DatasetInputTargets } from "./inputTargets";
import { LLMServiceIdentifier } from "./llmServiceIdentifier";

export type InputBenchmarkingBundle =
    InputBenchmarkingBundleImpl<InputBenchmarkingModelParams.Params>;

export interface InputBenchmarkingBundleImpl<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    llmServiceIdentifier: LLMServiceIdentifier;
    inputBenchmarkingModelsParams: InputParams[];
    requestedTargets: DatasetInputTargets;
}
