import { LLMService } from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { UserModelParams } from "../../../../llm/userModelParams";

import { DatasetInputTargets } from "../common/inputTargets";

import { InputBenchmarkingModelParams } from "./inputBenchmarkingModelParams";

export interface ResolvedWithServiceBenchmarkingBundle {
    llmService: LLMService<UserModelParams, ModelParams>;
    inputBenchmarkingModelsParams: InputBenchmarkingModelParams.Params[];
    requestedTargets: DatasetInputTargets;
}
