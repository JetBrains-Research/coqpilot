import { SubprocessProofsChecker } from "../../benchmarkCompletionGeneration/proofsCheckers/subprocessProofsChecker";
import { SubprocessCoqProjectParser } from "../../parseDataset/coqProjectParser/subprocessCoqProjectParser";
import { ExperimentRunOptions } from "../../structures/experimentRunOptions";
import { InputBenchmarkingBundle } from "../../structures/inputBenchmarkingBundle";
import { AbstractExperiment, ExecutionContext } from "../abstractExperiment";

export class MultiWorkspacesExperiment extends AbstractExperiment {
    constructor(
        bundles: InputBenchmarkingBundle[] = [],
        sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {
        super(bundles, sharedRunOptions);
    }

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
