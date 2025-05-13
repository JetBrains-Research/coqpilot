import { LLMService } from "../../../../llm/llmServices/llmService";

import { DatasetInputTargets } from "../common/inputTargets";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export interface ResolvedWithServiceBenchmarkingBundle {
    llmService: LLMService;
    inputBenchmarkingModelsParams: InputBenchmarkingModelParams.Params[];
    requestedTargets: DatasetInputTargets;
}
