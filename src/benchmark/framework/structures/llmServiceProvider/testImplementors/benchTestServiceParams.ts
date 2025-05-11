import { AnalyzedChatHistory } from "../../../../../llm/llmServices/commonStructures/chat";
import {
    SchedulersProvider,
    SchedulersProviderBuilders,
} from "../../../../../llm/llmServices/commonStructures/schedulersProviders";
import { LLMServiceInternal } from "../../../../../llm/llmServices/llmServiceInternal";
import {
    ResolvedLLMServiceParams,
    resolveServiceParamsWithDefaults,
} from "../../../../../llm/llmServices/llmServiceParams";

import { delay } from "../../../../../utils/async/delay";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../../../logging/benchmarkingLogger";

import { BenchTestModelParams } from "./benchTestModelParams";
import { BenchTestService } from "./benchTestService";

export type GenerateRawProofsType = (
    analyzedChat: AnalyzedChatHistory,
    params: BenchTestModelParams,
    choices: number,
    logger: BenchmarkingLogger
) => Promise<string[]>;

export type BenchTestServiceParams = Partial<ResolvedBenchTestServiceParams>;

export interface ResolvedBenchTestServiceParams
    extends ResolvedLLMServiceParams {
    logger: BenchmarkingLogger;
    generateRawProofs: GenerateRawProofsType;
    getSchedulersProvider: (service: BenchTestService) => SchedulersProvider;
}

export function resolveBenchTestServiceParamsWithDefaults(
    serviceParams: BenchTestServiceParams
): ResolvedBenchTestServiceParams {
    return {
        ...resolveServiceParamsWithDefaults(serviceParams),
        logger:
            serviceParams.logger ??
            new BenchmarkingLoggerImpl(
                SeverityLevel.DEBUG,
                undefined,
                "[Benchmarking Test Service]"
            ),
        generateRawProofs:
            serviceParams.generateRawProofs ??
            BenchTestDefaults.generateRawProofs,
        getSchedulersProvider: (service: BenchTestService) =>
            SchedulersProviderBuilders.unlimitedParallelism<BenchTestModelParams>(
                service.fullName,
                false
            ),
    };
}

export namespace BenchTestDefaults {
    export async function generateRawProofs(
        _analyzedChat: AnalyzedChatHistory,
        params: BenchTestModelParams,
        choices: number
    ): Promise<string[]> {
        LLMServiceInternal.validateChoices(choices);
        if (params.generationMillis !== 0) {
            await delay(params.generationMillis);
        }
        return params.tactics.slice(0, choices);
    }
}
