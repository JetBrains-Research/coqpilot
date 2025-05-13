import { LLMServiceIdentifier } from "../../llm/llmServices/llmServiceIdentifier";
import {
    PredefinedProofsUserModelParams,
    UserModelParams,
} from "../../llm/userModelParams";

export type InputModelsParams = InputModelsParamsItem<UserModelParams>[];

export interface InputModelsParamsItem<T extends UserModelParams> {
    identifier: LLMServiceIdentifier;
    models: T[];
}

export const onlyAutoModelsParams: InputModelsParams = [
    {
        identifier: LLMServiceIdentifier.PREDEFINED_PROOFS,
        models: [
            {
                modelId: "Predefined tactic",
                tactics: ["firstorder auto with *."],
            },
        ],
    } as InputModelsParamsItem<PredefinedProofsUserModelParams>,
];

export const tacticianModelsParams: InputModelsParams = [
    {
        identifier: LLMServiceIdentifier.PREDEFINED_PROOFS,
        models: [
            {
                modelId: "Tactician",
                tactics: ["synth."],
            },
        ],
    } as InputModelsParamsItem<PredefinedProofsUserModelParams>,
];
