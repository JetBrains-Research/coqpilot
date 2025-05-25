import { ProofProvider } from "../../../../proofProviders/impl/proofProvider";

import { DatasetInputTargets } from "../common/inputTargets";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export interface ResolvedWithProofProviderBenchmarkingBundle {
    proofProvider: ProofProvider;
    inputBenchmarkingModelsParams: InputBenchmarkingModelParams.Params[];
    requestedTargets: DatasetInputTargets;
}
