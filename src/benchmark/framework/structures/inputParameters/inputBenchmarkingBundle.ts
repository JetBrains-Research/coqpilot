import { ProofProviderConstructor } from "../../../../proofProviders/impl/proofProviderConstructor";

import { DatasetInputTargets } from "../common/inputTargets";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export type InputBenchmarkingBundle =
    InputBenchmarkingBundleImpl<InputBenchmarkingModelParams.Params>;

export interface InputBenchmarkingBundleImpl<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    proofProviderConstructor: ProofProviderConstructor;
    inputBenchmarkingModelsParams: InputParams[];
    requestedTargets: DatasetInputTargets;
}
