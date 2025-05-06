import { CoqLspProviderBuilder } from "../../../../coqLsp/coqLspProviders/coqLspProviderBuilders";

import { SeverityLevel } from "../../logging/benchmarkingLogger";
import { BenchmarkingOptions } from "../benchmarkingCore/benchmarkingOptions";

import { DatasetCacheUsageMode } from "./datasetCaching";

export interface ExperimentRunOptions extends BenchmarkingOptions {
    loggerSeverity: SeverityLevel;
    /**
     * Path relative to the root directory. If it set, logs will be written to this file.
     * Otherwise, they will be shown in the console.
     */
    logsFilePath: string | undefined;

    /**
     * Path to the coq-lsp server. Currently, it **must be set up properly**;
     * otherwise, proof checking always suceeds even for the invalid proofs.
     *
     * Notes on the coq-lsp server path resolution.
     * - If `coqLspServerPath` is set, it will be used.
     * - Otherwise, the one stored in the `COQ_LSP_PATH` environment variable will be selected.
     * - Finally, if none of them are set, coq-lsp will search for the server path automatically.
     */
    coqLspServerPath: string | undefined;

    datasetCacheUsage: DatasetCacheUsageMode;
    /**
     * Path relative to the root directory. If it is not set, a `dataset/.parsingCache` will be used.
     * Inside, the cached dataset projects are stored: for a project `dataset/example`,
     * its cache might be found inside `${datasetCacheDirectoryPath}/example`.
     *
     * Note: the benchmarking framework is allowed to modify `datasetCacheDirectoryPath` content
     * if the corresponding `datasetCacheUsage` mode is enabled.
     */
    datasetCacheDirectoryPath: string;

    maxActiveSubprocessesNumber: number;
    maxParallelGenerationRequestsToModel: number;

    buildAndParseCoqProjectSubprocessTimeoutMillis: number | undefined;
    checkProofsSubprocessTimeoutMillis: number | undefined;

    enableSubprocessLifetimeDebugLogs: boolean;

    enableSubprocessesSchedulingDebugLogs: boolean;
    enableModelsSchedulingDebugLogs: boolean;

    servicesMaxParallelism: LLMServicesMaxParallelism;

    /**
     * Control `coq-lsp` clients creation and usage.
     *
     * Use `CoqLspProviderBuilders` namespace to select one of the already implemented strategies.
     *
     * The default `coqLspProviderBuilder` for benchmarking frameworks is:
     * ```
     * CoqLspProviderBuilders.newCoqLspPerRequestWithLimitedParallelism(
     *     BenchmarkingOptionsDefaults.DEFAULT_MAX_RUNNING_COQ_LSP_CLIENTS
     * )
     * ```
     */
    coqLspProviderBuilder: CoqLspProviderBuilder;
}

export namespace ExperimentRunOptions {
    export interface ResolveOnStartup {
        loggerSeverity: SeverityLevel;
        logsFilePath: string | undefined;

        datasetCacheUsage: DatasetCacheUsageMode;
        datasetCacheDirectoryPath: string;
    }

    export type AfterStartupResolution = InputExperimentRunOptions &
        ResolveOnStartup;
}

export interface LLMServicesMaxParallelism {
    perOpenAiModelName: number;
    perGrazieModelName: number;
    perLmStudioPort: number;
    perDeepSeekModelName: number;
    rangoInstancesInParallel: number;
}

export type InputExperimentRunOptions = Omit<
    Partial<ExperimentRunOptions>,
    "servicesMaxParallelism"
> & {
    servicesMaxParallelism?: Partial<LLMServicesMaxParallelism>;
};
