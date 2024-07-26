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
     *
     * *Important:* DO NOT use this mode after modifying the source project,
     * that can cause undefined results. However, this mode is completely safe
     * when the source project stays unchanged.
     */
    EXTEND_CACHE_WITH_MISSING_TARGETS,

    /**
     * The requested projects cache will be fully cleared
     * and the requested targets only will be cached.
     *
     * Detailed exaplnation:
     * - all the requested targets will be parsed from the source projects;
     * - the requested projects cache will be cleared;
     * - the requested targets parsing results will be cached.
     */
    REBUILD_CACHE_FOR_REQUESTED_TARGETS,

    /**
     * The requested projects cache will be fully cleared
     * and the requested files will be cached completely.
     *
     * This mode is similar to the `REBUILD_CACHE_FOR_REQUESTED_TARGETS` one;
     * but instead of parsing only the requested targets,
     * it parses and caches **all targets** found in the requested files.
     */
    REBUILD_COMPLETE_CACHE_FOR_REQUESTED_FILES,

    /**
     * The requested projects cache will be fully cleared
     * and the requested projects will be cached completely.
     *
     * This mode is similar to the `REBUILD_CACHE_FOR_REQUESTED_TARGETS` one;
     * but instead of parsing only the requested targets,
     * it parses and caches **all source Coq files** of the requested projects.
     */
    REBUILD_COMPLETE_CACHE_FOR_REQUESTED_PROJECTS,
}
