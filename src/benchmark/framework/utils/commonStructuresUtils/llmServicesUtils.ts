import { ErrorsHandlingMode } from "../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { DeepSeekModelParamsResolver } from "../../../../llm/llmServices/deepSeek/deepSeekModelParamsResolver";
import { DeepSeekService } from "../../../../llm/llmServices/deepSeek/deepSeekService";
import { GrazieModelParamsResolver } from "../../../../llm/llmServices/grazie/grazieModelParamsResolver";
import { GrazieService } from "../../../../llm/llmServices/grazie/grazieService";
import { LLMService } from "../../../../llm/llmServices/llmService";
import { LLMServiceParams } from "../../../../llm/llmServices/llmServiceParams";
import { LMStudioModelParamsResolver } from "../../../../llm/llmServices/lmStudio/lmStudioModelParamsResolver";
import { LMStudioService } from "../../../../llm/llmServices/lmStudio/lmStudioService";
import {
    DeepSeekModelParams,
    GrazieModelParams,
    LMStudioModelParams,
    ModelParams,
    OpenAiModelParams,
    PredefinedProofsModelParams,
} from "../../../../llm/llmServices/modelParams";
import { OpenAiModelParamsResolver } from "../../../../llm/llmServices/openai/openAiModelParamsResolver";
import { OpenAiService } from "../../../../llm/llmServices/openai/openAiService";
import { PredefinedProofsModelParamsResolver } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsModelParamsResolver";
import { PredefinedProofsService } from "../../../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { RangoInstaller } from "../../../../llm/llmServices/rango/rangoInstaller";
import { RangoModelParamsResolver } from "../../../../llm/llmServices/rango/rangoModelParamsResolver";
import { RangoService } from "../../../../llm/llmServices/rango/rangoService";
import { ParamsResolverImpl } from "../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../llm/userModelParams";

import { EventLogger } from "../../../../logging/eventLogger";
import { unreachable } from "../../../../utils/errors/throwErrors";
import {
    CorrespondingInputServiceParams,
    CorrespondingServiceParams,
    LLMServiceStringIdentifier,
} from "../../structures/common/llmServiceIdentifier";
import { LLMServicesMaxParallelism } from "../../structures/inputParameters/experimentRunOptions";
import { InstallerProvider } from "../../structures/llmServiceProvider/installerProvider";
import {
    LimitedParallelismSchedulersProvider,
    SchedulersProvider,
    UnlimitedSchedulersProvider,
    createDefaultLLMServiceSchedulersProvider,
} from "../asyncUtils/schedulersProviders";

/**
 * Regardless of the string values defined in the implementation of `LLMServiceIdentifier` (they can change with time),
 * this function guarantees to provide nice and human-readable names of the services.
 */
export function getShortName(
    serviceIdentifier: LLMServiceStringIdentifier
): string {
    switch (serviceIdentifier) {
        case "predefined":
            return "Predefined Proofs";
        case "openai":
            return "Open AI";
        case "grazie":
            return "Grazie";
        case "lmstudio":
            return "LM Studio";
        case "deepseek":
            return "DeepSeek";
        case "rango":
            return "Rango";
    }
}

export type LLMServiceBuilder = (
    eventLogger: EventLogger | undefined,
    errorsHandlingMode: ErrorsHandlingMode
) => LLMService<UserModelParams, ModelParams>;

export function selectLLMServiceBuilder<T extends LLMServiceStringIdentifier>(
    serviceIdentifier: T,
    serviceParams?:
        | CorrespondingServiceParams<T>
        | CorrespondingInputServiceParams<T>
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
        case "predefined":
            return createBuilder(PredefinedProofsService);
        case "openai":
            return createBuilder(OpenAiService);
        case "grazie":
            return createBuilder(GrazieService);
        case "lmstudio":
            return createBuilder(LMStudioService);
        case "deepseek":
            return createBuilder(DeepSeekService);
        case "rango":
            return createBuilder(RangoService);
        default:
            unreachable(
                `unknown \`LLMServiceStringIdentifier\` "${serviceIdentifier}"`
            );
    }
}

export function selectInstallerProvider(
    serviceIdentifier: LLMServiceStringIdentifier
): InstallerProvider | undefined {
    switch (serviceIdentifier) {
        case "predefined":
        case "openai":
        case "grazie":
        case "lmstudio":
        case "deepseek":
            return undefined;
        case "rango":
            return () => {
                return {
                    installer: new RangoInstaller(),
                    options: undefined,
                };
            };
    }
}

export interface LLMServicesItems<ItemType> {
    predefinedProofs: ItemType;
    openAi: ItemType;
    grazie: ItemType;
    lmStudio: ItemType;
    deepSeek: ItemType;
    rango: ItemType;
}

export function selectLLMServiceItem<ItemType>(
    serviceIdentifier: LLMServiceStringIdentifier,
    items: LLMServicesItems<ItemType>
): ItemType {
    switch (serviceIdentifier) {
        case "predefined":
            return items.predefinedProofs;
        case "openai":
            return items.openAi;
        case "grazie":
            return items.grazie;
        case "lmstudio":
            return items.lmStudio;
        case "deepseek":
            return items.deepSeek;
        case "rango":
            return items.rango;
    }
}

export class LLMServicesItemsHolder<ItemType>
    implements LLMServicesItems<ItemType>
{
    readonly predefinedProofs!: ItemType;
    readonly openAi!: ItemType;
    readonly grazie!: ItemType;
    readonly lmStudio!: ItemType;
    readonly deepSeek!: ItemType;
    readonly rango!: ItemType;

    constructor(items: LLMServicesItems<ItemType>) {
        Object.assign(this, items);
    }

    select(serviceIdentifier: LLMServiceStringIdentifier): ItemType {
        return selectLLMServiceItem(serviceIdentifier, this);
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
                    new UnlimitedSchedulersProvider<PredefinedProofsModelParams>(
                        `Models Scheduler: ${getShortName("predefined")} Service, unlimited parallelism`,
                        enableLogs
                    ),
                openAi: createDefaultLLMServiceSchedulersProvider(
                    maxParallelism.perOpenAiModelName,
                    (params: OpenAiModelParams) => params.modelName,
                    "openai",
                    enableLogs
                ),
                grazie: createDefaultLLMServiceSchedulersProvider(
                    maxParallelism.perGrazieModelName,
                    (params: GrazieModelParams) => params.modelName,
                    "grazie",
                    enableLogs
                ),
                lmStudio: createDefaultLLMServiceSchedulersProvider(
                    maxParallelism.perLmStudioPort,
                    (params: LMStudioModelParams) => params.port,
                    "lmstudio",
                    enableLogs
                ),
                deepSeek: createDefaultLLMServiceSchedulersProvider(
                    maxParallelism.perDeepSeekModelName,
                    (params: DeepSeekModelParams) => params.modelName,
                    "deepseek",
                    enableLogs
                ),
                rango: new LimitedParallelismSchedulersProvider(
                    maxParallelism.rangoInstancesInParallel,
                    `Models Scheduler: ${getShortName("rango")} Service, max ${maxParallelism.rangoInstancesInParallel} request per time`,
                    enableLogs
                ),
            });
        }
    })();
}
