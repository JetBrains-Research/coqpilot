import * as fs from "fs";
import * as path from "path";

import { UserModelsParams } from "../../llm/userModelParams";

import { BenchmarkResult, runTestBenchmark } from "./benchmarkingFramework";
import { code, consoleLogLine } from "./loggingUtils";
import { onlyAutoModelsParams } from "./presets";

interface Benchmark {
    name: string;
    items: DatasetItem[];
    modelsParams: UserModelsParams;
    requireAllAdmitsCompleted: Boolean;
    timeoutMinutes: number;
}

class DatasetItem {
    workspaceRootPath: string | undefined;

    /* Paths should be relative to 'dataset' folder */
    constructor(
        public path: string,
        workspaceRootPath: string | undefined = undefined
    ) {
        this.workspaceRootPath = workspaceRootPath;
    }
}

const simpleAutoBenchmark: Benchmark = {
    name: "Complete simple examples with `auto`",
    items: [new DatasetItem("auto_benchmark.v")],
    modelsParams: onlyAutoModelsParams,
    requireAllAdmitsCompleted: true,
    timeoutMinutes: 1,
};

const mixedAutoBenchmark: Benchmark = {
    name: "Complete mixed examples (both simple & hard) with `auto`",
    items: [new DatasetItem("mixed_benchmark.v")],
    modelsParams: onlyAutoModelsParams,
    requireAllAdmitsCompleted: false,
    timeoutMinutes: 1,
};

const immBenchmark: Benchmark = {
    name: "Complete imm with auto",
    items: [new DatasetItem("imm/src/basic/Events.v", "imm")],
    modelsParams: onlyAutoModelsParams,
    requireAllAdmitsCompleted: false,
    timeoutMinutes: 60,
};

const benchmarks: Benchmark[] = [
    simpleAutoBenchmark,
    mixedAutoBenchmark,
    immBenchmark,
];

suite("Benchmark", () => {
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
                            benchmark.modelsParams,
                            resolvedWorkspaceRootPath,
                            benchmark.requireAllAdmitsCompleted
                        );
                    admitsCompletedInTotal.add(admitsCompleted);
                    theoremsProvedInTotal.add(theoremsProved);
                }
            }

            consoleLogLine();
            consoleLogLine("\n");
            console.log(
                `${code("magenta")}BENCHMARK REPORT:${code("reset")} ${benchmark.name}`
            );
            console.log(
                `- ADMITS COMPLETED IN TOTAL: ${admitsCompletedInTotal}`
            );
            console.log(
                `- THEOREMS PROVED IN TOTAL: ${theoremsProvedInTotal}\n`
            );
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
