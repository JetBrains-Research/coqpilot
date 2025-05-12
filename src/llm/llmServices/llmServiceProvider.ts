import { unreachable } from "../../utils/errors/throwErrors";
import { UserModelParams } from "../userModelParams";

import { DeepSeekService } from "./deepSeek/deepSeekService";
import { GrazieService } from "./grazie/grazieService";
import { LLMService } from "./llmService";
import {
    CorrespondingInputServiceParams,
    LLMServiceIdentifier,
} from "./llmServiceIdentifier";
import { LMStudioService } from "./lmStudio/lmStudioService";
import { ModelParams } from "./modelParams";
import { OpenAiService } from "./openai/openAiService";
import { PredefinedProofsService } from "./predefinedProofs/predefinedProofsService";
import { RangoService } from "./rango/rangoService";
import { LLMServiceControlParams } from "./utils/llmServiceControlParams";

export type LLMServiceProvider = (
    controlParams: LLMServiceControlParams
) => LLMService<UserModelParams, ModelParams>;

export function selectLLMServiceProvider<T extends LLMServiceIdentifier>(
    serviceIdentifier: T,
    inputServiceParams: CorrespondingInputServiceParams<T>
): LLMServiceProvider {
    function createProvider(
        serviceCtor: new (
            inputServiceParams?: CorrespondingInputServiceParams<T>
        ) => LLMService<UserModelParams, ModelParams>
    ): LLMServiceProvider {
        return (controlParams) =>
            new serviceCtor({
                ...inputServiceParams,
                ...controlParams,
            });
    }
    switch (serviceIdentifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return createProvider(PredefinedProofsService);
        case LLMServiceIdentifier.OPENAI:
            return createProvider(OpenAiService);
        case LLMServiceIdentifier.GRAZIE:
            return createProvider(GrazieService);
        case LLMServiceIdentifier.LMSTUDIO:
            return createProvider(LMStudioService);
        case LLMServiceIdentifier.DEEPSEEK:
            return createProvider(DeepSeekService);
        case LLMServiceIdentifier.RANGO:
            return createProvider(RangoService);
    }
    unreachable(`unknown \`serviceIdentifier\`: ${serviceIdentifier}`);
}
