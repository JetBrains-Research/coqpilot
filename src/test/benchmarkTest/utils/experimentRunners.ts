import { expect } from "earl";

import {
    BenchmarkingBundleWithModelsParams,
    BenchmarkingBundleWithTargets,
} from "../../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { SingleWorkspaceExperiment } from "../../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../../benchmark/framework/logging/benchmarkingLogger";
import { ExperimentResults } from "../../../benchmark/framework/structures/benchmarkingResults/experimentResults";
import { DatasetInputTargets } from "../../../benchmark/framework/structures/common/inputTargets";
import { DatasetCacheUsageMode } from "../../../benchmark/framework/structures/inputParameters/datasetCaching";
import { colorize } from "../../../utils/colorLogging";
import { unreachable } from "../../../utils/errors/throwErrors";
import { createRelativeTmpDir } from "../../commonTestFunctions/pathsResolver";

export async function runSimpleTestExperiment(
    experiment: SingleWorkspaceExperiment
): Promise<ExperimentResults> {
    let results: ExperimentResults | undefined = undefined;
    try {
        results = await experiment.run(createRelativeTmpDir(), {
            loggerSeverity: SeverityLevel.ERROR,
            datasetCacheUsage: DatasetCacheUsageMode.NO_CACHE_USAGE,
            proofGenerationRetries: 1,
            failFast: true,
        });
    } catch (error) {
        console.error(
            colorize(`\nExperiment pipeline has failed: ${error}\n`, "red")
        );
    }
    expect(results).not.toBeNullish();
    return results ?? unreachable("`expect` checked nullability before");
}

export function buildExperimentWithBundles(
    ...bundles: BenchmarkingBundleWithTargets<any>[]
): SingleWorkspaceExperiment {
    const experiment = new SingleWorkspaceExperiment();
    bundles.forEach((bundle) => bundle.addTo(experiment));
    return experiment;
}

export async function runSimpleTestExperimentWithBundles(
    ...bundles: BenchmarkingBundleWithTargets<any>[]
): Promise<ExperimentResults> {
    const experiment = buildExperimentWithBundles(...bundles);
    return await runSimpleTestExperiment(experiment);
}

export async function runSimpleTestExperimentWithTargetsAndModels(
    testTargets: DatasetInputTargets,
    ...models: BenchmarkingBundleWithModelsParams<any>[]
): Promise<ExperimentResults> {
    const bundles = models.map((model) => model.withTargets(testTargets));
    const experiment = buildExperimentWithBundles(...bundles);
    return await runSimpleTestExperiment(experiment);
}
