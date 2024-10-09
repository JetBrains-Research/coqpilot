import { ExperimentResults } from "../../structures/benchmarkingResults/experimentResults";
import { ExperimentRunOptions } from "../../structures/inputParameters/experimentRunOptions";
import { LightweightSerialization } from "../lightweightItems/lightweightSerialization";
import { LightweightSerializer } from "../lightweightItems/lightweightSerializer";
import { MultiWorkspacesExperiment } from "../multiWorkspacesExperiment";

/**
 * An `Experiment` to specify and generate input to the large-scale benchmarking pipeline executed in TeamCity.
 * See `this.buildLightweightBenchmarkingItems(...)` method for more details.
 *
 * Due to `TeamCityExperiment`'s role, it does not support running benchmarks locally and `this.run(...)` method throws an error.
 *
 * This class extends `MultiWorkspacesExperiment`; therefore, it can be used with multiple workspaces per call.
 */
export class TeamCityExperiment extends MultiWorkspacesExperiment {
    /**
     * Builds lightweight benchmarking items for the requested targets and saves them into `outputDirectoryPath`.
     * The returning promise resolves successfully if and only if the operation succeeded.
     *
     * *Warning:* `outputDirectoryPath` content will be cleared before saving the built lightweight benchmarking items.
     *
     * This operation is used as the first step for the large-scale benchmarking pipeline executed in TeamCity.
     * The goal is to resolve input for the benchmarks (specified via the setup DSL) into **separate** benchmarking items
     * that can be stored in the repository **efficiently**.
     *
     * The output `outputDirectoryPath` will have the following structure after the operation is successfully finished:
     * - `projects` subfolder: `[workspace path descriptor].json` files with `LightweightWorkspaceRoot` objects;
     * - `models` subfolder: `[modelId].json` files with `LightweightInputModelParams` objects;
     * - `items` subfolder: `[task descriptor].json` files with `LightweightBenchmarkingItem` objects.
     *
     * *Note on the efficiency of the operation.*
     * Unfortunately, calling this operation requires the requested dataset projects being built,
     * even though the next pipeline step (executed remotely) will need to build them again. However:
     * 1. The key importance of the `buildLightweightBenchmarkingItems` is to prepare *separate* benchmarking items:
     *    that requires parsing source files, for example, to find all requested admits. Thus, this step could not be ommitted.
     * 2. In practice, projects building and parsing can be skipped in case of dataset cache being present.
     *    Therefore, building dataset projects should be done only once locally and then reused with no overhead.
     *
     * *Implementation note*. So far this method simply builds the complete benchmarking items the same way as it is done
     * in the core `AbstractExperiment.run(...)` method and then serializes them in their lightweight versions.
     * Although the "unneccesary" model parameters resolution takes place ("unneccessary", because the models
     * will be saved unresolved for the sake of data storage efficiency), it actually validates the parameters specified by a user,
     * preventing such errors from being propagated to the large-scale pipeline itself.
     *
     * @param outputDirectoryPath a directory path relative to the root directory to save lightweight serialization into.
     * @param runOptions properties to update the options for **this** build with. To save the updated options for the further operations use `AbstractExperiment.updateRunOptions(...)` method instead.
     */
    async buildLightweightBenchmarkingItems(
        outputDirectoryPath: string,
        runOptions: Partial<ExperimentRunOptions> = {}
    ) {
        const [requestedTargets, executionContext] =
            this.prepareExecutionContextFromInputTargets(
                {
                    ...this.sharedRunOptions,
                    ...runOptions,
                },
                "[Building Lightweight Benchmarking Items]",
                (logger) =>
                    TeamCityExperiment.mergeAndResolveRequestedTargets(
                        this.bundles,
                        logger
                    )
            );
        const benchmarkingItems = await this.buildBenchmarkingItems(
            requestedTargets,
            executionContext
        );

        const serialization = LightweightSerializer.serializeToLightweight(
            benchmarkingItems,
            this.bundles
        );
        LightweightSerialization.logSerialization(
            "Successfully prepared lightweight serialization:",
            serialization,
            executionContext.logger
        );
        LightweightSerializer.saveSerializationToDirectory(
            serialization,
            outputDirectoryPath,
            executionContext.logger
        );
    }

    /**
     * `TeamCityExperiment` **does not support** running benchmarks locally;
     * therefore this method throws an error.
     */
    async run(
        _artifactsDirPath: string,
        _runOptions: Partial<ExperimentRunOptions> = {}
    ): Promise<ExperimentResults> {
        throw Error(
            "TeamCityExperiment does not support running benchmarks locally"
        );
    }
}
