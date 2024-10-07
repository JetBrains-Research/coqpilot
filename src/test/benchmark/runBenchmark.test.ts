import * as fs from "fs";
import * as path from "path";

import { AdditionalFileImport } from "./additionalImports";
import { BenchmarkResult, runTestBenchmark } from "./benchmarkingFramework";
import { InputModelsParams } from "./inputModelsParams";
import { BenchmarkReportHolder } from "./reportHolder";
import { DatasetItem } from "./utils/datasetConstructionUtils";
import {
    code,
    consoleLog,
    consoleLogSeparatorLine,
} from "./utils/loggingUtils";

interface Benchmark {
    name: string;
    items: DatasetItem[];
    inputModelsParams: InputModelsParams;
    requireAllAdmitsCompleted: Boolean;
    benchmarkFullTheorems: Boolean;
    benchmarkAdmits: Boolean;
    timeoutMinutes: number;
    groupName: string;
    additionalImports?: AdditionalFileImport[];
    // The maximum number of premises used as a few-shot
    // prompt for the model.
    // If undefined, no limit is set and all possible premises
    // that fit into the context window will be used.
    maxPremisesNumber?: number;
    // When using additional tools, issued for Coq, this timeout is used
    // to define how long do we wait for the proof to be generated.
    perProofTimeoutMillis: number;
}

// const resPath = path.join(
//     __dirname,
//     "../../../src/test/benchmark/benchmarkPrivate/resources/test.json"
// );
const reportPath = path.join(
    __dirname,
    "../../../src/test/benchmark/report.json"
);
// const immBenchmark: Benchmark = {
//     name: "Benchmark predef tactics in IMM group A",
//     items: datasetFromJson(resPath, "imm"),
//     inputModelsParams: onlyAutoModelsParams,
//     requireAllAdmitsCompleted: false,
//     benchmarkFullTheorems: true,
//     benchmarkAdmits: false,
//     timeoutMinutes: 1000,
//     groupName: "A",
// Uncomment the following line to enable additional imports.
// This is necessary if you want to generate completion with
// an additional solver.
// additionalImports: [
//     AdditionalFileImport.tactician(),
//     AdditionalFileImport.coqHammer(),
// ],
//     maxPremisesNumber: undefined,
//     perProofTimeoutMillis: 30000,
// };

const benchmarks: Benchmark[] = [];

suite("Benchmark", () => {
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
                            benchmark.maxPremisesNumber,
                            benchmark.groupName,
                            reportHolder,
                            benchmark.additionalImports,
                            benchmark.perProofTimeoutMillis
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
