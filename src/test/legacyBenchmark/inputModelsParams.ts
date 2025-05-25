import { ProofProviderIdentifier } from "../../proofProviders/impl/proofProviderIdentifier";
import {
    PredefinedProofsUserModelParams,
    UserModelParams,
} from "../../proofProviders/userModelParams";

export type InputModelsParams = InputModelsParamsItem<UserModelParams>[];

export interface InputModelsParamsItem<T extends UserModelParams> {
    identifier: ProofProviderIdentifier;
    models: T[];
}

export const onlyAutoModelsParams: InputModelsParams = [
    {
        identifier: ProofProviderIdentifier.PREDEFINED_PROOFS,
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
        identifier: ProofProviderIdentifier.PREDEFINED_PROOFS,
        models: [
            {
                modelId: "Tactician",
                tactics: ["synth."],
            },
        ],
    } as InputModelsParamsItem<PredefinedProofsUserModelParams>,
];
