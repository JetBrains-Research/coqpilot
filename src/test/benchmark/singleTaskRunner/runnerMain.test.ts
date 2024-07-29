import { ModelParams } from "../../../llm/llmServices/modelParams";
import { resolveOrThrow } from "../../../llm/llmServices/utils/resolveOrThrow";

import {
    BenchmarkingLogger,
    BenchmarkingLoggerImpl,
} from "../../../benchmark/framework/logging/benchmarkingLogger";
import { BenchmarkingModelParams } from "../../../benchmark/framework/structures/benchmarkingModelParams";
import { deserializeCodeElementPosition } from "../../../benchmark/framework/structures/utilStructures";
import {
    getDatasetDir,
    joinPaths,
    readFile,
    resolveAsAbsolutePath,
} from "../../../benchmark/framework/utils/fsUtils";
import {
    createParamsResolvers,
    getParamsResolver,
} from "../../../benchmark/framework/utils/llmServicesUtils";
import { resolveTheoremsRanker } from "../../../benchmark/framework/utils/resolveTheoremsRanker";
import { getRootDir } from "../../commonTestFunctions/pathsResolver";

import { SingleTaskRunnerStructures } from "./benchmarking/benchmarkingTask";
import { SingleTaskRunner } from "./benchmarking/executeSingleBenchmarkingTask";
import { SingleTaskRunnerOptions } from "./runnerOptions";

// TODO: support as npm task CLI flags
const exampleInputDirPath =
    "src/test/resources/benchmarking/singleTaskRunnerExampleInput";
const runnerOptionsPath = `${exampleInputDirPath}/runnerOptions.json`;
const benchmarkingTaskPath = `${exampleInputDirPath}/inputTask.json`;
const cachedSourceFileDataPath = `${exampleInputDirPath}/cached_auto_benchmark.json`;

suite("[Single Task Benchmark: Run Benchmark]", () => {
    test("Execute single task benchmarking", async () => {
        const runnerOptions =
            parseFromFile<SingleTaskRunnerOptions.RunnerOptions>(
                resolveAsAbsolutePath(runnerOptionsPath)
            );
        const task = parseAndBuildBenchmarkingTask(
            resolveAsAbsolutePath(benchmarkingTaskPath),
            resolveAsAbsolutePath(cachedSourceFileDataPath)
        );
        const logger = buildLogger(task, runnerOptions);

        await SingleTaskRunner.executeBenchmarkingTask(
            task,
            runnerOptions.execution,
            runnerOptions.saveResultToFilePath,
            logger
        );
    });
});

// TODO: move into separate file

function parseFromFile<T>(filePath: string): T {
    const content = readFile(filePath, (e) => {
        throw Error(`Failed to parse "${filePath}": ${e}`);
    });
    // TODO: validate with schema?
    return JSON.parse(content) as T;
}

function parseAndBuildBenchmarkingTask(
    taskFilePath: string,
    cachedSourceFileDataPath: string
): SingleTaskRunnerStructures.BenchmarkingTask {
    // Note: parsed source file shouldn't be specified inside this config, it will be read from parsing cache.
    const inputBenchmarkingTask =
        parseFromFile<SingleTaskRunnerStructures.InputBenchmarkingTask>(
            taskFilePath
        );
    return {
        target: inputBenchmarkingTask.target,
        params: resolveInputParams(inputBenchmarkingTask.inputParams),
        workspaceRootDirectoryPath:
            inputBenchmarkingTask.workspaceRootDirectoryPath,
        parsedSourceFile: parseCachedFileData(cachedSourceFileDataPath),
    };
}

function resolveInputParams(
    inputParams: SingleTaskRunnerStructures.InputBenchmarkingParams
): BenchmarkingModelParams<ModelParams> {
    const paramsResolver = getParamsResolver(
        inputParams.llmServiceIdentifier,
        createParamsResolvers() // TODO: optimize
    );
    const { ranker, ...pureInputModelParams } =
        inputParams.inputBenchmarkingModelsParams;
    return {
        theoremRanker: resolveTheoremsRanker(
            inputParams.inputBenchmarkingModelsParams.ranker
        ),
        modelParams: resolveOrThrow(paramsResolver, pureInputModelParams),
        llmServiceIdentifier: inputParams.llmServiceIdentifier, // TODO: validate
    };
}

function parseCachedFileData(
    cachedFileDataPath: string
): SingleTaskRunnerStructures.ParsedSourceFile {
    const parsedFileData =
        parseFromFile<SingleTaskRunnerStructures.ParsedSourceFile>(
            cachedFileDataPath
        );
    parsedFileData.filePath = joinPaths(
        getDatasetDir(),
        parsedFileData.filePath
    );
    return parsedFileData;
}

function buildLogger(
    task: SingleTaskRunnerStructures.BenchmarkingTask,
    runnerOptions: SingleTaskRunnerOptions.RunnerOptions
): BenchmarkingLogger {
    const baseLogger: BenchmarkingLogger = new BenchmarkingLoggerImpl(
        runnerOptions.loggerSeverity,
        runnerOptions.logsFilePath === undefined
            ? undefined
            : {
                  resolvedFilePath: resolveAsAbsolutePath(
                      joinPaths(getRootDir(), runnerOptions.logsFilePath)
                  ),
                  clearOnStart: true,
              },
        "[Single Task Benchmarking]"
    );
    return baseLogger.createChildLoggerWithIdentifier(
        [
            "[",
            `modelId: "${task.params.modelParams.modelId}", `,
            `theorem: \`${task.target.sourceTheoremName}\`, `,
            `completion position: ${deserializeCodeElementPosition(task.target.positionRange.start)}`,
            "]\n",
            `[file: ${task.parsedSourceFile.filePath}]`,
        ].join("")
    );
}
