import { expect } from "earl";

import { AnalyzedChatHistory } from "../../../proofProviders/impl/commonStructures/chat";

import {
    BenchTestInputBenchmarkingModelParams,
    BenchTestModelParams,
} from "../../../benchmark/framework/benchTest/benchTestModelParams";
import { BenchTestService } from "../../../benchmark/framework/benchTest/benchTestService";
import {
    BenchmarkingBundle,
    BenchmarkingBundleWithModelsParams,
} from "../../../benchmark/framework/experiment/setupDSL/benchmarkingBundleBuilder";
import { TargetsBuilder } from "../../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
    SeverityLevel,
} from "../../../benchmark/framework/logging/benchmarkingLogger";
import { InputBenchmarkingModelParams } from "../../../benchmark/framework/structures/inputParameters/inputBenchmarkingModelParams";

import { runSimpleTestExperimentWithBundle } from "./experimentRunners";
import { BenchmarkingTestsConstants } from "./testConstants";
import { TestTargetType, withTargetsFromFile } from "./testTargetTypeUtils";

import Constants = BenchmarkingTestsConstants;

export async function runSmokeTestExperimentWithBundle(
    modelsBundle: BenchmarkingBundleWithModelsParams<any>
) {
    const testTarget = new TargetsBuilder()
        .withWorkspaceRoot(
            Constants.TEST_DATASET_NAME,
            "no-special-environment"
        )
        .withAdmitTargetsFromFile("test.v", "test")
        .buildInputTargets();
    const completeBundle = modelsBundle.withTargets(testTarget);
    await runSimpleTestExperimentWithBundle(completeBundle);
}

export async function testContextTheoremsNotContainTarget(
    targetTheoremFilePath: string,
    targetTheoremName: string,
    targetType: TestTargetType,
    printContext: boolean = false
) {
    const testTarget = withTargetsFromFile(
        new TargetsBuilder().withWorkspaceRoot(
            Constants.TEST_DATASET_NAME,
            "no-special-environment"
        ),
        targetType,
        targetTheoremFilePath,
        targetTheoremName
    ).buildInputTargets();

    const bundle = new BenchmarkingBundle()
        .withCustomProofProvider<BenchTestInputBenchmarkingModelParams>(
            (controlParams) =>
                new BenchTestService({
                    ...controlParams,
                    logger: new BenchmarkingLoggerImpl(
                        SeverityLevel.DEBUG,
                        undefined,
                        `[Test context theorems must not contain the target one: "${targetTheoremName}" in ${targetTheoremFilePath}]`
                    ),
                    generateRawProofs: async (
                        analyzedChat: AnalyzedChatHistory,
                        params: BenchTestModelParams,
                        _choices: number,
                        logger: BenchmarkingLogger
                    ): Promise<string[]> => {
                        if (printContext) {
                            logger.debug(
                                `Context theorems: [${analyzedChat.contextTheorems.join(", ")}]`
                            );
                        }
                        const targetIsInContext =
                            analyzedChat.contextTheorems.find(
                                (contextTheoremName) =>
                                    contextTheoremName === targetTheoremName
                            ) !== undefined;
                        expect(targetIsInContext).toBeFalsy();
                        return params.tactics;
                    },
                })
        )
        .withBenchmarkingModelsParamsCommons({
            ranker: "random",
        })
        .withBenchmarkingModelsParams({
            generationMillis: 0,
            modelId: "dummy",
            tactics: ["auto."],
        })
        .withTargets(testTarget);

    await runSimpleTestExperimentWithBundle(bundle);
}

export async function testProveTheoremWithRango(
    targetTheoremFilePath: string,
    rangoMockModel: BenchmarkingBundleWithModelsParams<InputBenchmarkingModelParams.RangoParams>
) {
    const testTarget = new TargetsBuilder()
        .withWorkspaceRoot(
            Constants.TEST_DATASET_NAME,
            "no-special-environment"
        )
        .withProveTheoremTargetsFromFile(targetTheoremFilePath, "test")
        .buildInputTargets();

    await runSimpleTestExperimentWithBundle(
        rangoMockModel.withTargets(testTarget)
    );
}
