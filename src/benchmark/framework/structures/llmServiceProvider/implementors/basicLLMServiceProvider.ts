import { ErrorsHandlingMode } from "../../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { LLMServiceParams } from "../../../../../llm/llmServices/llmServiceParams";
import { ModelParams } from "../../../../../llm/llmServices/modelParams";
import { ParamsResolverImpl } from "../../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../../llm/userModelParams";

import { EventLogger } from "../../../../../logging/eventLogger";
import { AsyncScheduler } from "../../../../../utils/async/asyncScheduler";
import { invariantFailed } from "../../../../../utils/errors/throwErrors";
import { JsonSpacing, toJsonString } from "../../../../../utils/printers";
import { getShortName } from "../../../utils/commonStructuresUtils/llmServicesUtils";
import {
    CorrespondingInputServiceParams,
    LLMServiceIdentifier,
    LLMServiceStringIdentifier,
} from "../../common/llmServiceIdentifier";
import { InstallerProvider } from "../installerProvider";
import { LLMServiceProvider } from "../llmServiceProvider";

import {
    selectInstallerProvider,
    selectLLMServiceBuilder,
} from "./llmServicesProfile";
import {
    BasicModelsSchedulersOptions,
    LLMServicesParamsResolvers,
    LLMServicesSchedulersProviders,
    createParamsResolvers,
    createSchedulersProviders,
} from "./llmServicesProfile";

export class BasicLLMServiceProvider extends LLMServiceProvider {
    constructor(
        readonly serviceIdentifier: LLMServiceIdentifier,
        readonly serviceParams?: CorrespondingInputServiceParams<LLMServiceStringIdentifier>
    ) {
        super();
    }

    protected readonly selfClass = BasicLLMServiceProvider;

    static readonly serializationType = "basicProvider";
    static {
        LLMServiceProvider.registerSelfSerialization(
            this.serializationType,
            BasicLLMServiceProvider
        );
    }

    constructService(
        eventLogger: EventLogger | undefined,
        errorsHandlingMode: ErrorsHandlingMode
    ) {
        return selectLLMServiceBuilder(
            this.serviceIdentifier,
            this.serviceParams
        )(eventLogger, errorsHandlingMode);
    }

    getInstallerProvider(): InstallerProvider | undefined {
        return selectInstallerProvider(this.serviceIdentifier);
    }

    private static readonly paramsResolvers: LLMServicesParamsResolvers =
        createParamsResolvers();

    getParamsResolver(): ParamsResolverImpl<UserModelParams, ModelParams> {
        return BasicLLMServiceProvider.paramsResolvers.select(
            this.serviceIdentifier
        );
    }

    toLogString(verbose: boolean): string {
        const serviceParamsString =
            this.serviceParams === undefined || !verbose
                ? ""
                : ` ${toJsonString(this.serviceParams, JsonSpacing.UNFORMATTED)}`;
        return `${getShortName(this.serviceIdentifier)}${serviceParamsString}`;
    }

    static setSchedulersProvidersSettings(
        schedulersSettings: BasicModelsSchedulersOptions
    ) {
        this._schedulersSettings = schedulersSettings;
    }

    selectScheduler(modelParams: ModelParams): AsyncScheduler {
        return BasicLLMServiceProvider.accessSchedulersProviders()
            .select(this.serviceIdentifier)
            .getScheduler(modelParams);
    }

    private static _schedulersProviders:
        | LLMServicesSchedulersProviders
        | undefined = undefined;

    private static _schedulersSettings:
        | BasicModelsSchedulersOptions
        | undefined = undefined;

    private static accessSchedulersProviders(): LLMServicesSchedulersProviders {
        if (this._schedulersProviders === undefined) {
            this._schedulersProviders = createSchedulersProviders(
                this._schedulersSettings ??
                    invariantFailed(
                        "`BasicLLMServiceProvider`",
                        "`BasicLLMServiceProvider._schedulersProviders` is accessed before ",
                        "setting schedulers-providers settings"
                    )
            );
        }
        return this._schedulersProviders;
    }

    serializeData(): BasicLLMServiceProviderSerializedData {
        return {
            service: this.serviceIdentifier,
            serviceParams: this.serviceParams,
        };
    }

    static deserialize(serializedProviderData: any): LLMServiceProvider {
        // TODO: would be nice to validate data, at least somehow
        return new BasicLLMServiceProvider(
            serializedProviderData.service,
            serializedProviderData.serviceParams
        );
    }
}

interface BasicLLMServiceProviderSerializedData {
    service: LLMServiceIdentifier;
    serviceParams?: LLMServiceParams;
}
