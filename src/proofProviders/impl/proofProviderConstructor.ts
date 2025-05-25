import { unreachable } from "../../utils/errors/throwErrors";

import { DeepSeekService } from "./deepSeek/deepSeekService";
import { GrazieService } from "./grazie/grazieService";
import { LMStudioService } from "./lmStudio/lmStudioService";
import { OpenAiService } from "./openai/openAiService";
import { PredefinedProofsProvider } from "./predefinedProofs/predefinedProofsProvider";
import { ProofProvider } from "./proofProvider";
import {
    CorrespondingInputProofProviderParams,
    ProofProviderIdentifier,
} from "./proofProviderIdentifier";
import { RangoService } from "./rango/rangoService";
import { ProofProviderControlParams } from "./utils/proofProviderControlParams";

export type ProofProviderConstructor = (
    controlParams: ProofProviderControlParams
) => ProofProvider;

export function selectProofProviderConstructor<
    T extends ProofProviderIdentifier,
>(
    proofProviderIdentifier: T,
    inputServiceParams: CorrespondingInputProofProviderParams<T>
): ProofProviderConstructor {
    function createConstructor(
        proofProviderCtor: new (
            inputServiceParams?: CorrespondingInputProofProviderParams<T>
        ) => ProofProvider
    ): ProofProviderConstructor {
        return (controlParams) =>
            new proofProviderCtor({
                ...inputServiceParams,
                ...controlParams,
            });
    }
    switch (proofProviderIdentifier) {
        case ProofProviderIdentifier.PREDEFINED_PROOFS:
            return createConstructor(PredefinedProofsProvider);
        case ProofProviderIdentifier.OPENAI:
            return createConstructor(OpenAiService);
        case ProofProviderIdentifier.GRAZIE:
            return createConstructor(GrazieService);
        case ProofProviderIdentifier.LMSTUDIO:
            return createConstructor(LMStudioService);
        case ProofProviderIdentifier.DEEPSEEK:
            return createConstructor(DeepSeekService);
        case ProofProviderIdentifier.RANGO:
            return createConstructor(RangoService);
    }
    unreachable(
        `unknown \`proofProviderIdentifier\`: ${proofProviderIdentifier}`
    );
}
