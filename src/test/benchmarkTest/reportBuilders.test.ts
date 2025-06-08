import { expect } from "earl";

import { PredefinedProofsUserModelParams } from "../../proofProviders/userModelParams";

import { ModelsToAggregatedGroups } from "../../benchmark/framework/reportBuilders/modelsToAggregatedGroupsTable/report";
import { ReportBuilders } from "../../benchmark/framework/reportBuilders/reportBuilders";
import { CompletionGenerationTask } from "../../benchmark/framework/structures/benchmarkingCore/completionGenerationTask";
import { ExperimentResults } from "../../benchmark/framework/structures/benchmarkingResults/experimentResults";
import { buildErrorCompleteLog } from "../../utils/errors/errorsUtils";
import { throwError } from "../../utils/errors/throwErrors";
import { readFile } from "../../utils/fs/fileUtils";
import { joinPaths, resolveAsAbsolutePath } from "../../utils/fs/pathUtils";
import { createTmpDirectory } from "../../utils/fs/tmpFs";
import { getResourcesDir } from "../commonTestFunctions/pathsResolver";

import { runReportsBuilderExperiment } from "./utils/specificTestsImpl";
import { BenchmarkingTestsConstants } from "./utils/testConstants";

import Constants = BenchmarkingTestsConstants;

interface NamedOptions {
    name: string;
    options: Partial<ModelsToAggregatedGroups.Options>;
}

interface Finalizator {
    name: string;
    fileExt: string;
    buildReport: (
        report: ModelsToAggregatedGroups.Report,
        outputFilePath: string | undefined
    ) => string;
}

suite("[Benchmarking Framework Tests] Report builders tests", () => {
    const reportsTmpDir = createTmpDirectory();

    function testReportBuilder(
        builderName: string,
        expectedContentRelFilePath: string,
        buildReport: (
            results: ExperimentResults,
            outputFilePath: string | undefined
        ) => string
    ) {
        test(`Test ${builderName}`, async () => {
            const resolvedExpectedContentFilePath = resolveAsAbsolutePath(
                joinPaths(
                    getResourcesDir(),
                    "expectedReports",
                    expectedContentRelFilePath
                )
            );
            const expectedContent = readFile(
                resolvedExpectedContentFilePath,
                (err) =>
                    throwError(
                        "failed to read expected content file, ",
                        `cause: ${buildErrorCompleteLog(err)}`
                    )
            );

            const results = await runReportsBuilderExperiment(models);

            // Check string and file outputs returns the same
            const contentBuiltAsString = buildReport(results, undefined);
            const builtReportFilePath = buildReport(
                results,
                joinPaths(reportsTmpDir, expectedContentRelFilePath)
            );
            const contentReadFromFile = readFile(builtReportFilePath, (err) =>
                throwError(
                    "failed to read built file, ",
                    `cause: ${buildErrorCompleteLog(err)}`
                )
            );
            expect(contentBuiltAsString).toEqual(contentReadFromFile);

            // Check content is correct
            expect(contentBuiltAsString).toEqual(expectedContent);
        }).timeout(Constants.SIMPLE_TEST_TIMEOUT);
    }

    function testModelsToGroupsTable(
        namedOptions: NamedOptions,
        finalizator: Finalizator,
        expectedContentRelFilePath: string
    ) {
        const buildReport = (results: ExperimentResults) =>
            ReportBuilders.modelsToAggregatedGroupsTable(
                results,
                namedOptions.options
            );
        testReportBuilder(
            `\`modelsToAggregatedGroupsTable\`, ${namedOptions.name} options, \`${finalizator.name}\``,
            expectedContentRelFilePath,
            (results, outputFilePath) =>
                finalizator.buildReport(buildReport(results), outputFilePath)
        );
    }

    const models: PredefinedProofsUserModelParams[] = [
        { modelId: "Invalid proof", tactics: ["a."] },
        { modelId: "auto.", tactics: ["auto."] },
        { modelId: "reflexivity.", tactics: ["reflexivity."] },
        { modelId: "inversion 1.", tactics: ["inversion 1."] },
        { modelId: "Excluded by options", tactics: ["a."] },
    ];

    /**
     * Test `modelsToAggregatedGroupsTable`
     */

    const groupsMapper = (task: CompletionGenerationTask) => {
        const theoremToGroup = new Map<string, string[]>([
            ["only_auto_th1", ["Provable with auto.", "Mixed"]],
            ["only_auto_th2", ["Provable with auto."]],
            [
                "auto_or_reflexivity_th",
                ["Provable with anything", "Provable with auto.", "Mixed"],
            ],
            ["only_inversion_th", ["Mixed"]],
            ["hard_th", ["Mixed"]],
        ]);
        return theoremToGroup.get(task.sourceTheorem.name) ?? [];
    };
    const namedOptions: NamedOptions[] = [
        { name: "default-no-groups", options: {} },
        {
            name: "default-with-groups",
            options: {
                groupsMapper: groupsMapper,
            },
        },
        {
            name: "specified",
            options: {
                groupsMapper: groupsMapper,
                modelsMapper: (params) => {
                    const modelId = params.modelParams.modelId;
                    return modelId === "Excluded by options"
                        ? undefined
                        : modelId;
                },
                extraAggregatedRows: [
                    {
                        name: `reflexivity. + inversion 1.`,
                        shouldAggregateModel: (params) => {
                            const modelId = params.modelParams.modelId;
                            return (
                                modelId === "reflexivity." ||
                                modelId === "inversion 1."
                            );
                        },
                    },
                ],
                showAggregatedCell: (successes, total) =>
                    `${successes} / ${total}`,
            },
        },
    ];
    const finalizators: Finalizator[] = [
        {
            name: "markdown",
            fileExt: ".md",
            buildReport: (report, outputFilePath) =>
                report.toMarkdown(outputFilePath),
        },
        {
            name: "latex",
            fileExt: ".tex",
            buildReport: (report, outputFilePath) =>
                report.toLatex(outputFilePath),
        },
    ];

    for (const optionsItem of namedOptions) {
        for (const finalizator of finalizators) {
            testModelsToGroupsTable(
                optionsItem,
                finalizator,
                `${optionsItem.name}-${finalizator.name}${finalizator.fileExt}`
            );
        }
    }

    /**
     * TODO: test `toBasicJson` via serialization-deserialization cycle
     * (testing by comparison with the expected file is not feasible due to elapsed time values)
     */
});
