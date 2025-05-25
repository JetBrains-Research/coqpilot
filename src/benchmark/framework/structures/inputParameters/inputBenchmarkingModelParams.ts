import { ProofProviderIdentifier } from "../../../../proofProviders/impl/proofProviderIdentifier";
import {
    DeepSeekUserModelParams,
    GrazieUserModelParams,
    LMStudioUserModelParams,
    OpenAiUserModelParams,
    PredefinedProofsUserModelParams,
    RangoUserModelParams,
    UserModelParams,
} from "../../../../proofProviders/userModelParams";

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

export type CorrespondingInputParams<T extends ProofProviderIdentifier> =
    T extends ProofProviderIdentifier.PREDEFINED_PROOFS
        ? InputBenchmarkingModelParams.PredefinedProofsParams
        : T extends ProofProviderIdentifier.OPENAI
          ? InputBenchmarkingModelParams.OpenAiParams
          : T extends ProofProviderIdentifier.GRAZIE
            ? InputBenchmarkingModelParams.GrazieParams
            : T extends ProofProviderIdentifier.LMSTUDIO
              ? InputBenchmarkingModelParams.LMStudioParams
              : T extends ProofProviderIdentifier.DEEPSEEK
                ? InputBenchmarkingModelParams.DeepSeekParams
                : T extends ProofProviderIdentifier.RANGO
                  ? InputBenchmarkingModelParams.RangoParams
                  : never;
