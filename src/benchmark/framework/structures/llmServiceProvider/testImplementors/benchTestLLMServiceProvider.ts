import { ErrorsHandlingMode } from "../../../../../llm/llmServices/commonStructures/errorsHandlingMode";
import { InstallerProvider } from "../../../../../llm/llmServices/commonStructures/installerProvider";
import {
    SchedulersProvider,
    UnlimitedSchedulersProvider,
} from "../../../../../llm/llmServices/commonStructures/schedulersProviders";
import { LLMService } from "../../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../../llm/llmServices/modelParams";
import { ParamsResolverImpl } from "../../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../../llm/userModelParams";

import { EventLogger } from "../../../../../logging/eventLogger";
import { AsyncScheduler } from "../../../../../utils/async/asyncScheduler";
import { unsupported } from "../../../../../utils/errors/throwErrors";
import { LLMServiceProvider } from "../llmServiceProvider";
import { toOneLineLogString } from "../utils/toLog";

import {
    BenchTestModelParams,
    BenchTestModelParamsResolver,
} from "./benchTestModelParams";
import { BenchTestService } from "./benchTestService";
import { BenchTestServiceParams } from "./benchTestServiceParams";

export class BenchTestServiceProvider extends LLMServiceProvider {
    protected selfClass = BenchTestServiceProvider;

    static readonly serializationType = "benchTest";
    static {
        LLMServiceProvider.registerSelfSerialization(
            this.serializationType,
            BenchTestServiceProvider
        );
    }

    static readonly shortName = "Benchmarking Test";

    constructor(
        private readonly serviceParams: BenchTestServiceParams = {},
        private readonly schedulersProvider: SchedulersProvider = new UnlimitedSchedulersProvider<BenchTestModelParams>(
            `Models Scheduler: ${BenchTestServiceProvider.shortName} Service, unlimited parallelism`,
            false
        )
    ) {
        super();
    }

    constructService(
        eventLogger: EventLogger | undefined,
        errorsHandlingMode: ErrorsHandlingMode
    ): LLMService<UserModelParams, ModelParams> {
        return new BenchTestService({
            ...this.serviceParams,
            eventLogger: eventLogger,
            errorsHandlingMode: errorsHandlingMode,
        });
    }

    getInstallerProvider(): InstallerProvider | undefined {
        return undefined;
    }

    getParamsResolver(): ParamsResolverImpl<UserModelParams, ModelParams> {
        return new BenchTestModelParamsResolver();
    }

    selectScheduler(modelParams: ModelParams): AsyncScheduler {
        return this.schedulersProvider.getScheduler(modelParams);
    }

    toLogString(verbose: boolean): string {
        return toOneLineLogString(
            BenchTestServiceProvider.shortName,
            this.serviceParams,
            verbose
        );
    }

    serializeData(): {} {
        return {};
    }

    static deserialize(_serializedProviderData: any): LLMServiceProvider {
        unsupported(
            "Deserialization of `BenchTestService` is currently unsupported"
        );
    }
}
