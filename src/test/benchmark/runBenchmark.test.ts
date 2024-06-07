import * as fs from "fs";
import * as path from "path";

import { BenchmarkResult, runTestBenchmark } from "./benchmarkingFramework";
import { InputModelsParams, grazieModelsParams } from "./inputModelsParams";
import { code, consoleLog, consoleLogSeparatorLine } from "./loggingUtils";
import { BenchmarkReportHolder } from "./reportHolder";

interface Benchmark {
    name: string;
    items: DatasetItem[];
    inputModelsParams: InputModelsParams;
    requireAllAdmitsCompleted: Boolean;
    benchmarkFullTheorems: Boolean;
    benchmarkAdmits: Boolean;
    timeoutMinutes: number;
    groupName: string;
    // The maximum number of premises used as a few-shot
    // prompt for the model.
    // If undefined, no limit is set and all possible premises
    // that fit into the context window will be used.
    maximumUsedPremisesAmount?: number;
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

const mixedAutoBenchmark: Benchmark = {
    name: "Complete mixed examples (both simple & hard) with `auto`",
    items: [new DatasetItem("mixed_benchmark.v")],
    inputModelsParams: grazieModelsParams,
    requireAllAdmitsCompleted: false,
    benchmarkFullTheorems: true,
    benchmarkAdmits: false,
    timeoutMinutes: 1,
    groupName: "A",
    maximumUsedPremisesAmount: undefined,
};

const benchmarks: Benchmark[] = [mixedAutoBenchmark];

suite("Benchmark", () => {
    const reportPath = path.join(__dirname, "../../../report.json");
    const reportHolder = new BenchmarkReportHolder(reportPath);

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
                    const { admitsCompleted, theoremsProved } =
                        await runTestBenchmark(
                            resolvedFilePath,
                            benchmark.inputModelsParams,
                            item.path,
                            item.specificTheoremForBenchmark,
                            benchmark.benchmarkFullTheorems,
                            benchmark.benchmarkAdmits,
                            resolvedWorkspaceRootPath,
                            benchmark.requireAllAdmitsCompleted,
                            benchmark.maximumUsedPremisesAmount,
                            benchmark.groupName,
                            reportHolder
                        );
                    admitsCompletedInTotal.add(
                        admitsCompleted ?? new BenchmarkResult(0, 0)
                    );
                    theoremsProvedInTotal.add(
                        theoremsProved ?? new BenchmarkResult(0, 0)
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

            reportHolder.generateMarkdown();
        }).timeout(benchmark.timeoutMinutes * 60 * 1000);
    }
});

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
