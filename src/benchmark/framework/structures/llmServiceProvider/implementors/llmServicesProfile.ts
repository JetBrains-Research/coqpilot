import { ErrorsHandlingMode } from "../../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { InstallerProvider } from "../../../../../llm/llmServices/commonStructures/installerProvider";
import {
    SchedulersProvider,
    SchedulersProviderBuilders,
} from "../../../../../llm/llmServices/commonStructures/schedulersProviders";
import { DeepSeekModelParamsResolver } from "../../../../../llm/llmServices/deepSeek/deepSeekModelParamsResolver";
import { DeepSeekService } from "../../../../../llm/llmServices/deepSeek/deepSeekService";
import { GrazieModelParamsResolver } from "../../../../../llm/llmServices/grazie/grazieModelParamsResolver";
import { GrazieService } from "../../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../../llm/llmServices/llmService";
import { LLMServiceParams } from "../../../../../llm/llmServices/llmServiceParams";
import { LMStudioModelParamsResolver } from "../../../../../llm/llmServices/lmStudio/lmStudioModelParamsResolver";
import { LMStudioService } from "../../../../../llm/llmServices/lmStudio/lmStudioService";
import {
    DeepSeekModelParams,
    GrazieModelParams,
    LMStudioModelParams,
    ModelParams,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "../../../../../llm/llmServices/modelParams";
import { OpenAiModelParamsResolver } from "../../../../../llm/llmServices/openai/openAiModelParamsResolver";
import { OpenAiService } from "../../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../../../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { RangoInstaller } from "../../../../../llm/llmServices/rango/rangoInstaller";
import { RangoModelParamsResolver } from "../../../../../llm/llmServices/rango/rangoModelParamsResolver";
import { RangoService } from "../../../../../llm/llmServices/rango/rangoService";
import { ParamsResolverImpl } from "../../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../../llm/userModelParams";

import { EventLogger } from "../../../../../logging/eventLogger";
import { LLMServicesItemsHolder } from "../../../utils/commonStructuresUtils/llmServicesUtils";
import { LLMServiceIdentifier } from "../../common/llmServiceIdentifier";
import { LLMServicesMaxParallelism } from "../../inputParameters/experimentRunOptions";

export type LLMServiceBuilder = (
    eventLogger: EventLogger | undefined,
    errorsHandlingMode: ErrorsHandlingMode
) => LLMService<UserModelParams, ModelParams>;

export function selectLLMServiceBuilder(
    serviceIdentifier: LLMServiceIdentifier,
    serviceParams?: LLMServiceParams
): LLMServiceBuilder {
    function createBuilder(
        serviceCtor: new (
            serviceParams?: LLMServiceParams
        ) => LLMService<UserModelParams, ModelParams>
    ): LLMServiceBuilder {
        return (eventLogger, errorsHandlingMode) =>
            new serviceCtor({
                ...serviceParams,
                eventLogger: eventLogger,
                errorsHandlingMode: errorsHandlingMode,
            });
    }
    switch (serviceIdentifier) {
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

export function selectInstallerProvider(
    serviceIdentifier: LLMServiceIdentifier
): InstallerProvider | undefined {
    switch (serviceIdentifier) {
        case LLMServiceIdentifier.PREDEFINED_PROOFS:
        case LLMServiceIdentifier.OPENAI:
        case LLMServiceIdentifier.GRAZIE:
        case LLMServiceIdentifier.LMSTUDIO:
        case LLMServiceIdentifier.DEEPSEEK:
            return undefined;
        case LLMServiceIdentifier.RANGO:
            return () => {
                return {
                    installer: new RangoInstaller(),
                    options: undefined,
                };
            };
    }
}

export type LLMServicesParamsResolvers = LLMServicesItemsHolder<
    ParamsResolverImpl<UserModelParams, ModelParams>
>;

export function createParamsResolvers(): LLMServicesParamsResolvers {
    return new (class extends LLMServicesItemsHolder<
        ParamsResolverImpl<UserModelParams, ModelParams>
    > {
        constructor() {
            super({
                predefinedProofs: new PredefinedProofsModelParamsResolver(),
                openAi: new OpenAiModelParamsResolver(),
                grazie: new GrazieModelParamsResolver(),
                lmStudio: new LMStudioModelParamsResolver(),
                deepSeek: new DeepSeekModelParamsResolver(),
                rango: new RangoModelParamsResolver(),
            });
        }
    })();
}

export interface BasicModelsSchedulersOptions {
    enableModelsSchedulingDebugLogs: boolean;
    maxParallelism: LLMServicesMaxParallelism;
}

export type LLMServicesSchedulersProviders =
    LLMServicesItemsHolder<SchedulersProvider>;

export function createSchedulersProviders(
    settings: BasicModelsSchedulersOptions
): LLMServicesSchedulersProviders {
    const enableLogs = settings.enableModelsSchedulingDebugLogs;
    const maxParallelism = settings.maxParallelism;
    return new (class extends LLMServicesItemsHolder<SchedulersProvider> {
        constructor() {
            super({
                predefinedProofs:
                    SchedulersProviderBuilders.unlimitedParallelism<PredefinedProofsModelParams>(
                        LLMServiceIdentifier.PREDEFINED_PROOFS,
                        enableLogs
                    ),
                openAi: SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
                    maxParallelism.perOpenAiModelName,
                    (params: OpenAiModelParams) => params.modelName,
                    LLMServiceIdentifier.OPENAI,
                    enableLogs
                ),
                grazie: SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
                    maxParallelism.perGrazieModelName,
                    (params: GrazieModelParams) => params.modelName,
                    LLMServiceIdentifier.GRAZIE,
                    enableLogs
                ),
                lmStudio:
                    SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
                        maxParallelism.perLmStudioPort,
                        (params: LMStudioModelParams) => params.port,
                        LLMServiceIdentifier.LMSTUDIO,
                        enableLogs
                    ),
                deepSeek:
                    SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
                        maxParallelism.perDeepSeekModelName,
                        (params: DeepSeekModelParams) => params.modelName,
                        LLMServiceIdentifier.DEEPSEEK,
                        enableLogs
                    ),
                rango: SchedulersProviderBuilders.limitParallelismGlobally(
                    maxParallelism.rangoInstancesInParallel,
                    LLMServiceIdentifier.RANGO,
                    enableLogs
                ),
            });
        }
    })();
}
