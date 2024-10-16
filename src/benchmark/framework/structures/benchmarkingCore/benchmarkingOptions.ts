export interface BenchmarkingOptions {
    /**
     * If set to `true`, any error that occurs during the benchmarking process will cause
     * the entire pipeline to fail, halting the execution of all subsequent tasks.
     *
     * In more details, if `failFast` is set, the `benchmark` function behaves as follows:
     * - if any task fails with an error, this task's `Promise` will be rejected;
     * - all tasks execution will be stopped as soon as any task `Promise` rejects.
     */
    failFast: boolean;

    logFailFastTasksAborting: boolean;

    /**
     * If `undefined`, the retries number will not be limited.
     */
    proofGenerationRetries: number | undefined;

    logTeamCityStatistics: boolean;
}
