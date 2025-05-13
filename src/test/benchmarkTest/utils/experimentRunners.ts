import { expect } from "earl";

import { BenchmarkingBundleWithTargets } from "../../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { SingleWorkspaceExperiment } from "../../../benchmark/framework/experiment/singleWorkspaceExperiment";
import { SeverityLevel } from "../../../benchmark/framework/logging/benchmarkingLogger";
import { DatasetCacheUsageMode } from "../../../benchmark/framework/structures/inputParameters/datasetCaching";
import { colorize } from "../../../utils/colorLogging";
import { createRelativeTmpDir } from "../../commonTestFunctions/pathsResolver";

export function buildExperimentWithBundle(
    bundle: BenchmarkingBundleWithTargets<any>
): SingleWorkspaceExperiment {
    const experiment = new SingleWorkspaceExperiment();
    bundle.addTo(experiment);
    return experiment;
}

export async function runSimpleTestExperiment(
    experiment: SingleWorkspaceExperiment
) {
    let hasSuccessfullyFinished = false;
    try {
        await experiment.run(createRelativeTmpDir(), {
            loggerSeverity: SeverityLevel.ERROR,
            datasetCacheUsage: DatasetCacheUsageMode.NO_CACHE_USAGE,
            proofGenerationRetries: 1,
            failFast: true,
        });
        hasSuccessfullyFinished = true;
    } catch (error) {
        console.error(
            colorize(`\nExperiment pipeline has failed: ${error}\n`, "red")
        );
    }
    expect(hasSuccessfullyFinished).toBeTruthy();
}

export async function runSimpleTestExperimentWithBundle(
    bundle: BenchmarkingBundleWithTargets<any>
) {
    const experiment = buildExperimentWithBundle(bundle);
    await runSimpleTestExperiment(experiment);
}
