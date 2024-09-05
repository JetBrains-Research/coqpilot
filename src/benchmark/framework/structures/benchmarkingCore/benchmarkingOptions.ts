export interface BenchmarkingOptions {
    /**
     * If `undefined`, the retries number will not be limited.
     */
    proofGenerationRetries: number | undefined;

    logTeamCityStatistics: boolean;
}
