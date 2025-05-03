import { asLLMServices } from "../../../../llm/llmServices";
import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { DeepSeekModelParamsResolver } from "../../../../llm/llmServices/deepSeek/deepSeekModelParamsResolver";
import { DeepSeekService } from "../../../../llm/llmServices/deepSeek/deepSeekService";
import { GrazieModelParamsResolver } from "../../../../llm/llmServices/grazie/grazieModelParamsResolver";
import { GrazieService } from "../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { LLMServiceParams } from "../../../../llm/llmServices/llmServiceParams";
import { LMStudioModelParamsResolver } from "../../../../llm/llmServices/lmStudio/lmStudioModelParamsResolver";
import { LMStudioService } from "../../../../llm/llmServices/lmStudio/lmStudioService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { OpenAiModelParamsResolver } from "../../../../llm/llmServices/openai/openAiModelParamsResolver";
import { OpenAiService } from "../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { RangoModelParamsResolver } from "../../../../llm/llmServices/rango/rangoModelParamsResolver";
import { RangoService } from "../../../../llm/llmServices/rango/rangoService";
import { ParamsResolverImpl } from "../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../llm/userModelParams";

import { EventLogger } from "../../../../logging/eventLogger";
import { LLMServiceIdentifier } from "../../structures/common/llmServiceIdentifier";

/**
 * Regardless of the string values defined in the implementation of `LLMServiceIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the services.
 */
export function getShortName(identifier: LLMServiceIdentifier): string {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return "Predefined Proofs";
        case LLMServiceIdentifier.OPENAI:
            return "Open AI";
        case LLMServiceIdentifier.GRAZIE:
            return "Grazie";
        case LLMServiceIdentifier.LMSTUDIO:
            return "LM Studio";
        case LLMServiceIdentifier.DEEPSEEK:
            return "DeepSeek";
        case LLMServiceIdentifier.RANGO:
            return "Rango";
    }
}

export type LLMServiceBuilder = (
    eventLogger: EventLogger | undefined,
    errorsHandlingMode: ErrorsHandlingMode
) => LLMService<UserModelParams, ModelParams>;

export function selectLLMServiceBuilder(
    identifier: LLMServiceIdentifier
): LLMServiceBuilder {
    function createBuilder(
        serviceCtor: new (
            serviceParams: LLMServiceParams
        ) => LLMService<UserModelParams, ModelParams>
    ): LLMServiceBuilder {
        return (eventLogger, errorsHandlingMode) =>
            new serviceCtor({
                eventLogger: eventLogger,
                errorsHandlingMode: errorsHandlingMode,
            });
    }
    asLLMServices;
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return createBuilder(PredefinedProofsService);
        case LLMServiceIdentifier.OPENAI:
            return createBuilder(OpenAiService);
        case LLMServiceIdentifier.GRAZIE:
            return createBuilder(GrazieService);
        case LLMServiceIdentifier.LMSTUDIO:
            return createBuilder(LMStudioService);
        case LLMServiceIdentifier.DEEPSEEK:
            return createBuilder(DeepSeekService);
        case LLMServiceIdentifier.RANGO:
            return createBuilder(RangoService);
    }
}

export interface LLMServicesParamsResolvers {
    predefinedProofsModelParamsResolver: PredefinedProofsModelParamsResolver;
    openAiModelParamsResolver: OpenAiModelParamsResolver;
    grazieModelParamsResolver: GrazieModelParamsResolver;
    lmStudioModelParamsResolver: LMStudioModelParamsResolver;
    deepSeekModelParamsResolver: DeepSeekModelParamsResolver;
    rangoModelParamsResolver: RangoModelParamsResolver;
}

export function createParamsResolvers(): LLMServicesParamsResolvers {
    return {
        predefinedProofsModelParamsResolver:
            new PredefinedProofsModelParamsResolver(),
        openAiModelParamsResolver: new OpenAiModelParamsResolver(),
        grazieModelParamsResolver: new GrazieModelParamsResolver(),
        lmStudioModelParamsResolver: new LMStudioModelParamsResolver(),
        deepSeekModelParamsResolver: new DeepSeekModelParamsResolver(),
        rangoModelParamsResolver: new RangoModelParamsResolver(),
    };
}

export function getParamsResolver(
    identifier: LLMServiceIdentifier,
    paramsResolvers: LLMServicesParamsResolvers
): ParamsResolverImpl<UserModelParams, ModelParams> {
    switch (identifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
            return paramsResolvers.predefinedProofsModelParamsResolver;
        case LLMServiceIdentifier.OPENAI:
            return paramsResolvers.openAiModelParamsResolver;
        case LLMServiceIdentifier.GRAZIE:
            return paramsResolvers.grazieModelParamsResolver;
        case LLMServiceIdentifier.LMSTUDIO:
            return paramsResolvers.lmStudioModelParamsResolver;
        case LLMServiceIdentifier.DEEPSEEK:
            return paramsResolvers.deepSeekModelParamsResolver;
        case LLMServiceIdentifier.RANGO:
            return paramsResolvers.rangoModelParamsResolver;
    }
}
