import { unsupported } from "../../../../utils/throwErrors";
import { TimeMark } from "../../benchmarkingCore/singleCompletionGeneration/measureTimeUtils";
import { ExperimentResults } from "../../structures/benchmarkingResults/experimentResults";
import { ExperimentRunOptions } from "../../structures/inputParameters/experimentRunOptions";
import { InputBenchmarkingBundle } from "../../structures/inputParameters/inputBenchmarkingBundle";
import { throwBenchmarkingError } from "../../utils/throwErrors";
import { LightweightDeserializer } from "../lightweightItems/lightweightDeserializer";
import { LightweightSerialization } from "../lightweightItems/lightweightSerialization";
import { CacheTargetsImpl } from "../setupDSL/datasetCacheBuilder";
import { SingleWorkspaceExperiment } from "../singleWorkspaceExperiment";

/**
 * An `Experiment` that executes single _task_ of the large-scale benchmarking pipeline in TeamCity.
 * See `this.executeLightweightBenchmarkingItems(...)` method for more details.
 *
 * Due to `TeamCityExperiment`'s role, it does not support running benchmarks via setup DSL and corresponding methods throw an error.
 *
 * This class extends `SingleWorkspaceExperiment`; therefore, it can be used only with a single workspace per run and
 * should be executed only inside the `test-electron` environment.
 */
export class TeamCityAgent extends SingleWorkspaceExperiment {
    // TODO: design a way to pass single benchmarking item to the agent
    constructor(
        private readonly forceOneBenchmarkingItemPerRun: boolean = true,
        sharedRunOptions: Partial<ExperimentRunOptions> = {}
    ) {
        super([], sharedRunOptions);
    }

    /**
     * Conducts the same benchmarking experiment as the core `AbstractExperiment.run` method does,
     * but with reading lightweight benchmarking items as input instead of interpreting the setup DSL specified by a user.
     *
     * **Important note:** current implementation requires the source files of the input lightweight items
     * to be present in cache. Thus, make sure `datasetCacheDirectoryPath` option is set properly to the prepared cache.
     *
     * @param inputDirectoryPath a directory to read lightweight serialization from. It should have the structure specified by `AbstractExperiment.buildLightweightBenchmarkingItems` method.
     * @param artifactsDirPath empty directory path relative to the root directory.
     * @param runOptions properties to update the options for **this** run with. To save the updated options for the further runs use `AbstractExperiment.updateRunOptions(...)` method instead.
     */
    async executeLightweightBenchmarkingItems(
        inputDirectoryPath: string,
        artifactsDirPath: string,
        runOptions: Partial<ExperimentRunOptions> = {}
    ) {
        const [serialization, executionContext] = this.prepareExecutionContext(
            {
                ...this.sharedRunOptions,
                ...runOptions,
            },
            "[Building Lightweight Benchmarking Items]",
            (logger) => {
                const serialization =
                    LightweightDeserializer.readSerializationFromDirectory(
                        inputDirectoryPath,
                        logger
                    );
                LightweightSerialization.logSerialization(
                    "Successfully parsed lightweight serialization:",
                    serialization,
                    logger
                );
                return serialization;
            },
            (serialization) =>
                serialization.projects.map(
                    (project) => project.relativeDirectoryPath
                )
        );
        const totalTime = new TimeMark();

        if (
            this.forceOneBenchmarkingItemPerRun &&
            this.checkSerializationWillProduceManyBenchmarkingItems(
                serialization
            )
        ) {
            throwBenchmarkingError(
                `Too many benchmarking items: input lightweight items ("${inputDirectoryPath}" directory) produce more than 1 benchmarking items`
            );
        }

        const benchmarkingItems =
            LightweightDeserializer.restoreBenchmarkingItems(
                serialization,
                executionContext.resolvedRunOptions.datasetCacheDirectoryPath,
                executionContext.logger
            );
        if (benchmarkingItems.length === 0) {
            throwBenchmarkingError(
                "No items to benchmark: make sure the experiment input is configured correctly"
            );
        }

        // Note: `await` is here for consistency with other execution methods
        return await this.executeBenchmarkingItems(
            benchmarkingItems,
            artifactsDirPath,
            executionContext,
            totalTime
        );
    }

    private checkSerializationWillProduceManyBenchmarkingItems(
        serialization: LightweightSerialization.PackedItems
    ): boolean {
        if (serialization.items.length > 1) {
            return true;
        }
        if (serialization.items.length === 0) {
            return false;
        }
        const singleLightweightItem = serialization.items[0];
        return singleLightweightItem.targetModelIds.length > 1;
    }

    /**
     * `TeamCityAgent` **does not support** running benchmarks via setup DSL;
     * therefore this method throws an error. Use `this.executeLightweightBenchmarkingItems(...)` instead.
     */
    addBundle(_newBundle: InputBenchmarkingBundle) {
        this.throwDoesNotSupportSetupDSL();
    }

    /**
     * `TeamCityAgent` **does not support** running benchmarks via setup DSL;
     * therefore this method throws an error. Use `this.executeLightweightBenchmarkingItems(...)` instead.
     */
    async buildDatasetCache(
        _datasetCacheDirectoryPath: string,
        ..._cacheTargetsBuilders: CacheTargetsImpl.CacheTargetsBuilder[]
    ) {
        this.throwDoesNotSupportSetupDSL();
    }

    /**
     * `TeamCityAgent` **does not support** running benchmarks via setup DSL;
     * therefore this method throws an error. Use `this.executeLightweightBenchmarkingItems(...)` instead.
     */
    async run(
        _artifactsDirPath: string,
        _runOptions: Partial<ExperimentRunOptions> = {}
    ): Promise<ExperimentResults> {
        this.throwDoesNotSupportSetupDSL();
    }

    private throwDoesNotSupportSetupDSL(): never {
        unsupported(
            "TeamCityExperiment does not support running benchmarks via setup DSL: execute lightweight benchmarking items instead"
        );
    }
}
