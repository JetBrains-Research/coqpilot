/**
 * In the first stage, the benchmarking framework builds and parses
 * the target dataset projects. Fortunately, parsing results can be cached
 * and reused on the subsequent benchmarks launches to skip the actual dataset parsing stage.
 * `DatasetCacheUsageMode` defines the cache policy that will be applied to the next benchmarks run.
 */
export enum DatasetCacheUsageMode {
    /**
     * Cache directory is fully ignored: neither cache will be used, nor updated.
     */
    NO_CACHE_USAGE,

    /**
     * Cache will be treated as read-only one.
     *
     * For the requested targets present in the cache,
     * no parsing actions will be made: cached data will be used instead.
     */
    READ_CACHE_ONLY,

    /**
     * Cache might be both read and extended.
     *
     * For the requested targets present in the cache,
     * no parsing actions will be made: cached data will be used instead.
     * However, for the requested targets missing in the cache,
     * parsing will be performed and the cache will be extended with these results.
     */
    EXTEND_CACHE_WITH_MISSING_TARGETS,

    /**
     * The requested projects cache will be fully rebuilt.
     *
     * First, the requested projects cache will be cleared.
     * Afterwards, all the requested targets will be parsed from the source projects
     * and these results will be cached.
     *
     * In other words, the old cache is replaced with a newly-built one.
     */
    REBUILD_CACHE_FOR_REQUESTED_PROJECTS,

    /**
     * The requested projects cache will be fully rebuilt.
     *
     * This mode is similar to the `REBUILD_CACHE_FOR_REQUESTED_PROJECTS` one;
     * but instead of parsing only the requested targets,
     * it parses and caches *all* source Coq files of the requested projects.
     */
    BUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS,

    /**
     * Cache will be fully rebuilt.
     *
     * This mode is similar to the `BUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS`,
     * but makes parsing and caching work for all the dataset projects.
     *
     * In other words, the cache directory, first, will be completely cleared,
     * and then for all the projects in the `dataset` directory complete caches will be built.
     */
    BUILD_COMPLETE_DATASET_CACHE,
}
