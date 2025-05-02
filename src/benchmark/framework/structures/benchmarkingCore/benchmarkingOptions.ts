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
    logAbortingTasks: boolean;

    /**
     * If `undefined`, the retries number will not be limited.
     */
    proofGenerationRetries: number | undefined;

    /**
     * If `undefined`, the default one specified by CoqPilot will be used (`300_000 ms`).
     *
     * Each source file to be parsed or to be used for checking a proof inside,
     * first, is needed to be opened as a text document by `coq-lsp`.
     * Basically, during this operation `coq-lsp` type-checks the file and
     * caches it to process further operations. Unfortunately, large files
     * might take significantly much more time to be type-checked;
     * for such cases, `openDocumentTimeoutMillis` can be increased.
     *
     * However, sometimes such a timeout might signalize about `coq-lsp`
     * not being able to properly type-check the file;
     * thus, it is better not to set this parameter to effectively infinite values.
     */
    openDocumentTimeoutMillis: number | undefined;
    /**
     * If `undefined`, the default one specified by CoqPilot will be used (`15_000 ms`).
     *
     * It is recommened to define and increase `proofCheckTimeoutMillis` value,
     * if `CoqProofChecker` does not manage to type-check a proof inside large input file
     * you are working with in the time limit set by default.
     *
     * However, sometimes such a timeout might signalize about `coq-lsp`
     * not being able to properly type-check the file;
     * thus, it is better not to set this parameter to effectively infinite values.
     */
    proofCheckTimeoutMillis: number | undefined;

    logTeamCityStatistics: boolean;
}
