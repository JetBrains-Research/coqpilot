import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
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
}
