import { expect } from "earl";
import * as fs from "fs";
import * as path from "path";

import { BenchmarkResult, runTestBenchmark } from "./benchmarkingFramework";
import { InputModelsParams, onlyAutoModelsParams } from "./inputModelsParams";
import {
    code,
    consoleLog,
    consoleLogSeparatorLine,
    consoleLoggingIsMuted,
} from "./loggingUtils";
import { Results } from "./results";

interface Benchmark {
    name: string;
    items: DatasetItem[];
    inputModelsParams: InputModelsParams;
    requireAllAdmitsCompleted: Boolean;
    benchmarkFullTheorems: Boolean;
    benchmarkAdmits: Boolean;
    timeoutMinutes: number;
}

class DatasetItem {
    workspaceRootPath: string | undefined;
    specificTheoremForBenchmark: string[] | undefined;

    /* Paths should be relative to 'dataset' folder */
    constructor(
        public path: string,
        specificTheoremForBenchmark: string[] | undefined = undefined,
        workspaceRootPath: string | undefined = undefined
    ) {
        this.workspaceRootPath = workspaceRootPath;
        this.specificTheoremForBenchmark = specificTheoremForBenchmark;
    }
}

const simpleAutoBenchmark: Benchmark = {
    name: "Complete simple examples with `auto`",
    items: [new DatasetItem("auto_benchmark.v")],
    inputModelsParams: onlyAutoModelsParams,
    requireAllAdmitsCompleted: true,
    benchmarkFullTheorems: true,
    benchmarkAdmits: true,
    timeoutMinutes: 1,
};

const mixedAutoBenchmark: Benchmark = {
    name: "Complete mixed examples (both simple & hard) with `auto`",
    items: [new DatasetItem("mixed_benchmark.v")],
    inputModelsParams: onlyAutoModelsParams,
    requireAllAdmitsCompleted: false,
    benchmarkFullTheorems: true,
    benchmarkAdmits: true,
    timeoutMinutes: 1,
};

const benchmarks: Benchmark[] = [simpleAutoBenchmark, mixedAutoBenchmark];

suite("Benchmark", () => {
    expect(consoleLoggingIsMuted).toEqual(false);
    const datasetDir = getDatasetDir();

    for (const benchmark of benchmarks) {
        test(benchmark.name, async () => {
            const admitsCompletedInTotal = new BenchmarkResult(0, 0);
            const theoremsProvedInTotal = new BenchmarkResult(0, 0);

            for (const item of benchmark.items) {
                const resolvedWorkspaceRootPath = item.workspaceRootPath
                    ? path.join(datasetDir, item.workspaceRootPath)
                    : undefined;

                const resolvedItemPath = path.join(datasetDir, item.path);
                const itemPathStats = getPathStats(resolvedItemPath);
                if (!itemPathStats.isDirectory() && !itemPathStats.isFile()) {
                    throw Error(`unsupported path type: ${item.path}`);
                }
                const resolvedFilePaths = itemPathStats.isDirectory()
                    ? findSourceFiles(resolvedItemPath)
                    : [resolvedItemPath];

                for (const resolvedFilePath of resolvedFilePaths) {
                    const { admitsCompletions, theoremsCompletions } =
                        await runTestBenchmark(
                            resolvedFilePath,
                            benchmark.inputModelsParams,
                            item.specificTheoremForBenchmark,
                            benchmark.benchmarkFullTheorems,
                            benchmark.benchmarkAdmits,
                            resolvedWorkspaceRootPath,
                            benchmark.requireAllAdmitsCompleted
                        );
                    admitsCompletedInTotal.add(
                        approachSummaryToCounter(admitsCompletions)
                    );
                    theoremsProvedInTotal.add(
                        approachSummaryToCounter(theoremsCompletions)
                    );
                }
            }

            consoleLogSeparatorLine();
            consoleLogSeparatorLine("\n");
            consoleLog(
                `${code("magenta")}BENCHMARK REPORT:${code("reset")} ${benchmark.name}`
            );
            consoleLog(
                `- ADMITS COMPLETED IN TOTAL: ${admitsCompletedInTotal}`
            );
            consoleLog(
                `- THEOREMS PROVED IN TOTAL: ${theoremsProvedInTotal}\n`
            );
        }).timeout(benchmark.timeoutMinutes * 60 * 1000);
    }
});

function approachSummaryToCounter(
    summary: Results.ApproachBenchmarkingSummary | undefined
): BenchmarkResult {
    return summary === undefined
        ? new BenchmarkResult(0, 0)
        : new BenchmarkResult(
              summary.benchmarkingResults.length,
              summary.successfulBenchmarkingResults.length
          );
}

function getDatasetDir(): string {
    const dirname: string = path.join(__dirname, "../../../");
    return path.join(dirname, "dataset");
}

function getPathStats(path: string): fs.Stats {
    return fs.lstatSync(path);
}

function findSourceFiles(directoryPath: string): string[] {
    let sourceFilePaths: string[] = [];
    function traverseDirectory(curDirectoryPath: string) {
        fs.readdirSync(curDirectoryPath).forEach((child) => {
            const childPath = path.join(curDirectoryPath, child);
            if (fs.statSync(childPath).isDirectory()) {
                traverseDirectory(childPath);
            } else {
                if (
                    path.extname(childPath) === ".v" &&
                    !childPath.endsWith("_cp_aux.v")
                ) {
                    sourceFilePaths.push(childPath);
                }
            }
        });
    }
    traverseDirectory(directoryPath);
    return sourceFilePaths;
}
