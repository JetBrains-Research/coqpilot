import { SubprocessProofsChecker } from "../benchmarkingCore/singleCompletionGeneration/proofsCheckers/subprocessProofsChecker";
import { SubprocessCoqProjectParser } from "../parseDataset/coqProjectParser/subprocessCoqProjectParser";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { InputBenchmarkingBundle } from "../structures/inputParameters/inputBenchmarkingBundle";

import { AbstractExperiment, ExecutionContext } from "./abstractExperiment";

/**
 * An `Experiment` implementation that uses subprocesses to operate across multiple dataset workspaces.
 *
 * Due to the overhead of managing subprocesses, `MultiWorkspacesExperiment` is generally slower
 * than `SingleWorkspaceExperiment`. However, since the subprocesses are created within the contexts
 * of of the target workspaces, this experiment can benchmark all of them in a single run
 * (including any LLMService, their models, and task scheduling across the selected workspaces).
 *
 * Future versions of `MultiWorkspacesExperiment` will aim to reduce subprocess overhead,
 * potentially making it an even more efficient option for large-scale benchmarks.
 *
 * In summary, `MultiWorkspacesExperiment` is designed to work with multiple workspaces per run,
 * making it better suited for large benchmarking experiments.
 */
export class MultiWorkspacesExperiment extends AbstractExperiment {
    constructor(
        bundles: InputBenchmarkingBundle[] = [],
        sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {
        super(bundles, sharedRunOptions);
    }

    protected validateExecutionContextOrThrow(_: ExecutionContext): void {}

    protected setupCoqProjectParser = (executionContext: ExecutionContext) =>
        new SubprocessCoqProjectParser(
            executionContext.subprocessesScheduler,
            executionContext.resolvedRunOptions.buildAndParseCoqProjectSubprocessTimeoutMillis,
            executionContext.resolvedRunOptions.enableSubprocessLifetimeDebugLogs
        );

    protected setupProofsChecker = (executionContext: ExecutionContext) =>
        new SubprocessProofsChecker(
            executionContext.subprocessesScheduler,
            executionContext.resolvedRunOptions.checkProofsSubprocessTimeoutMillis,
            executionContext.resolvedRunOptions.enableSubprocessLifetimeDebugLogs
        );
}
