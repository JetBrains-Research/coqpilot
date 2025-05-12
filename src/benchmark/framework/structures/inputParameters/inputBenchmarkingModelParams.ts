import { LLMServiceIdentifier } from "../../../../llm/llmServices/llmServiceIdentifier";
import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    RangoUserModelParams,
    UserModelParams,
} from "../../../../llm/userModelParams";

import { RankerType } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

export namespace InputBenchmarkingModelParams {
    export interface Params extends UserModelParams {
        ranker: RankerType;
    }

    export interface PredefinedProofsParams
        extends PredefinedProofsUserModelParams,
            Params {}

    export interface OpenAiParams extends OpenAiUserModelParams, Params {}

    export interface GrazieParams extends GrazieUserModelParams, Params {}

    export interface LMStudioParams extends LMStudioUserModelParams, Params {}

    export interface DeepSeekParams extends DeepSeekUserModelParams, Params {}

    export interface RangoParams extends RangoUserModelParams, Params {}
}

export type CorrespondingInputParams<T extends LLMServiceIdentifier> =
    T extends LLMServiceIdentifier.PREDEFINED_PROOFS
        ? InputBenchmarkingModelParams.PredefinedProofsParams
        : T extends LLMServiceIdentifier.OPENAI
          ? InputBenchmarkingModelParams.OpenAiParams
          : T extends LLMServiceIdentifier.GRAZIE
            ? InputBenchmarkingModelParams.GrazieParams
            : T extends LLMServiceIdentifier.LMSTUDIO
              ? InputBenchmarkingModelParams.LMStudioParams
              : T extends LLMServiceIdentifier.DEEPSEEK
                ? InputBenchmarkingModelParams.DeepSeekParams
                : T extends LLMServiceIdentifier.RANGO
                  ? InputBenchmarkingModelParams.RangoParams
                  : never;
