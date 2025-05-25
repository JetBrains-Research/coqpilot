import { AnalyzedChatHistory } from "../../../proofProviders/impl/commonStructures/chat";
import {
    SchedulersProvider,
    SchedulersProviderBuilders,
} from "../../../proofProviders/impl/commonStructures/schedulersProviders";
import { ProofProviderInternal } from "../../../proofProviders/impl/proofProviderInternal";
import {
    ResolvedProofProviderParams,
    resolveProofProviderParamsWithDefaults,
} from "../../../proofProviders/impl/proofProviderParams";

import { delay } from "../../../utils/async/delay";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../logging/benchmarkingLogger";

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
    extends ResolvedProofProviderParams {
    logger: BenchmarkingLogger;
    generateRawProofs: GenerateRawProofsType;
    getSchedulersProvider: (
        proofProvider: BenchTestService
    ) => SchedulersProvider;
}

export function resolveBenchTestServiceParamsWithDefaults(
    proofProviderParams: BenchTestServiceParams
): ResolvedBenchTestServiceParams {
    return {
        ...resolveProofProviderParamsWithDefaults(proofProviderParams),
        logger:
            proofProviderParams.logger ??
            new BenchmarkingLoggerImpl(
                SeverityLevel.DEBUG,
                undefined,
                "[Benchmarking Test Service]"
            ),
        generateRawProofs:
            proofProviderParams.generateRawProofs ??
            BenchTestDefaults.generateRawProofs,
        getSchedulersProvider: (proofProvider: BenchTestService) =>
            SchedulersProviderBuilders.unlimitedParallelism<BenchTestModelParams>(
                proofProvider.name,
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
        ProofProviderInternal.validateChoices(choices);
        if (params.generationMillis !== 0) {
            await delay(params.generationMillis);
        }
        return params.tactics.slice(0, choices);
    }
}
