# Benchmarking Framework Guide

To run the new benchmarks, follow these steps:

0. Ensure the target Coq code is in the `dataset` directory.
1. Choose the experiment type: _single-_ or _multi-_ workspaces.
2. Specify the input, pipeline, and experiment options using the setup DSL.
3. Run the experiment by executing the appropriate `npm` task.

Below are more details about each step.

# Table of Contents

- ⚡️ [Benchmarking Framework Guide](#benchmarking-framework-guide)
  - [About Dataset](#about-dataset)
  - [Select & Run Experiment](#select--run-experiment)
    - 🏠 [`SingleWorkspaceExperiment`](#singleworkspaceexperiment)
    - 🌍 [`MultiWorkspacesExperiment`](#multiworkspacesexperiment)
    - 👽 [TeamCity Experiment (coming soon)](#teamcity-experiment-coming-soon)
  - [Setting Up the Experiment Pipeline](#setting-up-the-experiment-pipeline)
    - 🪁 [Example Pipeline Explained](#example-pipeline-explained)
    - ⛹️ [Run Options](#run-options)
  - [Framework Maintenance](#framework-maintenance)

## About Dataset

The `dataset` directory contains subdirectories, each representing a separate workspace. A workspace typically corresponds to a full Coq project (e.g., built with Nix), but there is also a `standalone-source-files` directory containing individual Coq files.

Most importantly, each workspace can have its own Coq dependencies; therefore, you must first activate its environment to work with its files.

## Select & Run Experiment

Currently, two types of experiments are supported:

### `SingleWorkspaceExperiment`

This experiment must be run within the workspace environment, which the user activates and manages. For example, for the `imm` project built with Nix:

```bash
cd dataset/imm
nix-build # builds the 'imm' project
nix-shell # activates its environment
export COQ_LSP_PATH=$(which coq-lsp) # sets up the proper coq-lsp server path
cd ../..
npm run single-workspace-benchmark
```

While manual environment management is required, `SingleWorkspaceExperiment` offers the best performance and is ideal for small, preliminary experiments.

### `MultiWorkspacesExperiment`

This experiment can run across multiple workspaces, with the framework handling environment activation and switching automatically.

```bash
npm run multi-workspaces-benchmark
```

However, this process incurs a performance overhead due to subprocess execution. This will be optimized in future releases, so for now, use `MultiWorkspacesExperiment` only when there are no strict time constraints.

### TeamCity Experiment (coming soon)

Benchmarks can also be run in TeamCity, which is ideal for large-scale experiments. This feature is currently **under development**, coming in the next releases.

## Setting Up the Experiment Pipeline

Each experiment type has a corresponding setup file:

-   [singleWorkspaceSetup.test.ts](../../../src/test/benchmark/singleWorkspaceSetup.test.ts) for the single-workspace experiments;
-   [multiWorkspacesSetup.ts](../../../src/benchmark/multiWorkspacesSetup.ts) for the multi-workspaces experiments.

Modify the relevant file to configure the experiment. Example pipelines are provided in these files for reference.

### Example Pipeline Explained

Basically, the steps are the following.

First, create an experiment object. In this example we'll use the multi-workspaces one.

```TypeScript
const experiment = new MultiWorkspacesExperiment();
```

Next, define the input for benchmarking using _bundles_ and _target builders_. **Target builders** describe the piece of the dataset to be used.

```TypeScript
const standaloneTargets = new TargetsBuilder()
    .withStandaloneFilesRoot()
    .withAdmitTargetsFromFile("auto_benchmark.v", "test", "test_thr")
    .withAdmitTargetsFromFile("mixed_benchmark.v")
    .buildInputTargets();

const immTargets = new TargetsBuilder()
    .withWorkspaceRoot("imm", "nix")
    .withProveTheoremTargetsFromFile("src/imm/CombRelations.v")
    .withProveTheoremTargetsFromDirectory(
        "src/basic",
        "Events.v",
        "Execution.v"
    )
    .buildInputTargets();
```

**Bundles** combine the selected targets with model parameters for benchmarking.

```TypeScript
new BenchmarkingBundle()
    .withLLMService("predefined")
    .withBenchmarkingModelsParamsCommons({
        // here you can specify any properties of the model parameters
        // that will be used as default ones for the models below
        ranker: "random",
    })
    .withBenchmarkingModelsParams(
        { modelId: "invalid-proof", tactics: ["a."] },
        { modelId: "prove-with-auto", tactics: ["auto."] }
    )
    .withTargets(standaloneTargets, immTargets)
    .addTo(experiment); // don't forget to do it (!)
```

Once the input is ready, it is time to actually set up the pipeline.
The main method is `experiment.run(...)`, which executes the benchmark.

```TypeScript
// Specify the output directory for the raw results and reports,
// and override the default options if needed.

const results = await experiment.run("benchmarksOutput", {
    datasetCacheDirectoryPath: "benchmarkLogs/.cache/",
    datasetCacheUsage: DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS,
    loggerSeverity: SeverityLevel.DEBUG,
    // ..., check all possible options further in this guide
});
```

Although all the results are automatically saved into the output directory, you can query the `results` object to access it in the code.

As you've noticed, dataset parsing can be cached to speed up future runs slightly. You can either build and use cache through the `datasetCacheUsage` option (check [`DatasetCacheUsageMode`](../../../src/benchmark/framework/structures/inputParameters/datasetCaching.ts) for more details), or prepare it explicitly via the special command:

```TypeScript
// Specify the output directory and the cache targets through the special builders.

await experiment
    .buildDatasetCache(
        "benchmarkLogs/.cache/",
        CacheTargets.standaloneFiles()
            .files("auto_benchmark.v", "mixed_benchmark.v")
            .directories("example-subdirectory-to-cache")
    )
```

**Important:** Most experiment commands are `async`, so use `await` or chain them with promises to avoid early termination. Check the setup files for examples.

### Run Options

Experiment behavior can be finely controlled using run options, which can be specified either per method (e.g. `experiment.run(...)`) or globally via `experiment.updateRunOptions(...)`.

```TypeScript
experiment.updateRunOptions({
    // The verbodity of the logs shown in the console or saved in the file.
    loggerSeverity: SeverityLevel.INFO,

    // Path relative to the root directory - if it set, logs will be written to this file.
    // Otherwise, they will be shown in the console.
    logsFilePath: "benchmarkLogs/experimentLogs",

    // Check `DatasetCacheUsageMode` for more details on the cache usage.
    datasetCacheUsage: DatasetCacheUsageMode.EXTEND_CACHE_WITH_MISSING_TARGETS,
    // Path relative to the root directory, where the dataset cache is stored.
    datasetCacheDirectoryPath: "benchmarkLogs/.cache/",

    // If set to `true`, any error that occurs during the benchmarking process will cause
    // the entire pipeline to fail, halting the execution of all subsequent tasks.
    failFast: false,
    // Additional logging to watch the task being aborted due to the fail-fast strategy.
    logFailFastTasksAborting: false,

    // Max number of proof-generation retries for each benchmarking task.
    // Can be left `undefined` to make the retries unlimited.
    proofGenerationRetries: 10,

    // Timeout for `coq-lsp` to type-check a source Coq file.
    // Such type-check is needed to be performed
    // before parsing a file or checking a new proof inside it.
    // Can be left `undefined` to use the default value set by CoqPilot.
    openDocumentTimeoutMillis: 300_000,

    // Timeout for `CoqProofChecker` to check a proof.
    // Can be left `undefined` to use the default value set by CoqPilot.
    proofCheckTimeoutMillis: 10_000;

    // There might be many parallel proof-generation requests to the same model
    // (in terms of model type, for example, "gpt-4o" models from OpenAI service),
    // and it might be useful to limit their number to guarantee the overall system progress.
    maxParallelGenerationRequestsToModel: 1,

    // Determines the max number of subprocesses working in parallel.
    // This parameter is relevant only for the multi-workspaces experiment
    // and is recommended to be set to 1 (due to the current `test-electron` limitations).
    maxActiveSubprocessesNumber: 1,

    // Two timeout parameters relevant only for the multi-workspaces experiment.
    // Recommended to be left `undefined` for the default values.
    buildAndParseCoqProjectSubprocessTimeoutMillis: 20_000,
    checkProofsSubprocessTimeoutMillis: 10_000,

    // Additional logging, that is usable for the debugging purposes only.
    enableSubprocessLifetimeDebugLogs: false,
    enableSubprocessesSchedulingDebugLogs: true,
    enableModelsSchedulingDebugLogs: true,

    // Additional logging for TeamCity agent to schedule tasks properly.
    logTeamCityStatistics: false,
});
```

All options have reasonable defaults (check their docs for details), so adjust only what’s necessary.

## Framework Maintenance

The benchmarking framework is still in the testing phase, so bugs and missing features are expected. Please report issues to [@GlebSolovev](https://github.com/GlebSolovev) or through GitHub issues.

_Upcoming improvements:_

-   multiround proof-generation support;
-   results reporting configuration;
-   CoqHammer and Tactician support;
-   experiment recovery (after failure or interruption);
-   large-scale experiment in TeamCity;
-   mutlispaces experiment optimization: more efficient subproccesses architecture;
-   arbitrary theorem proof steps as benchmarking targets.
