import { LocalProofsChecker } from "../benchmarkingCore/singleCompletionGeneration/proofsCheckers/localProofsChecker";
import { LocalCoqProjectParser } from "../parseDataset/coqProjectParser/localCoqProjectParser";
import { ExperimentRunOptions } from "../structures/inputParameters/experimentRunOptions";
import { InputBenchmarkingBundle } from "../structures/inputParameters/inputBenchmarkingBundle";

import { AbstractExperiment, ExecutionContext } from "./abstractExperiment";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 *
 * An `Experiment` implementation that runs all benchmarking commands in the main process.
 *
 * Due to the elimination of subprocess maintenance overhead,
 * `SingleWorkspaceExperiment` is typically much faster than `MultiWorkspacesExperiment`.
 * However, to execute all operations within a single process,
 * this experiment is limited to a single dataset workspace.
 * Moreover, it **must be run from within the context of the target workspace**.
 * For example, in the case of a Nix project, `SingleWorkspaceExperiment` should be executed from inside `nix-shell`.
 *
 * In summary, `SingleWorkspaceExperiment` is designed to work with only one workspace per run.
 */
export class SingleWorkspaceExperiment extends AbstractExperiment {
    constructor(
        bundles: InputBenchmarkingBundle[] = [],
        sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {
        super(bundles, sharedRunOptions);
    }

    protected validateExecutionContextOrThrow(
        executionContext: ExecutionContext
    ): void {
        if (executionContext.requestedWorkspaces.length > 1) {
            const workspacesList =
                executionContext.requestedWorkspaces.join(", ");
            throw Error(
                [
                    "The `SingleWorkspaceExperiment` targets must belong to the same workspace,",
                    "within the context of which the benchmark was executed.",
                    `However, the selected workspace targets are: [${workspacesList}].`,
                ].join(" ")
            );
        }
    }

    protected setupCoqProjectParser = (_: ExecutionContext) =>
        new LocalCoqProjectParser();

    protected setupProofsChecker = (_: ExecutionContext) =>
        new LocalProofsChecker();
}
