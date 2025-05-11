import { AsyncScheduler } from "../../../utils/async/asyncScheduler";
import { getOrPut } from "../../../utils/collectionUtils/mapUtils";
import { ModelParams } from "../modelParams";

export interface SchedulersProvider {
    getScheduler(modelParams: ModelParams): AsyncScheduler;
}

/**
 * Maintains a separate `AsyncScheduler` per model key (extracted by `extractKey`),
 * each limiting parallelism by `maxParallelRequestsToKey`.
 */
export class LimitedByKeyParallelismSchedulersProvider<
    ResolvedModelParams extends ModelParams,
    K,
> implements SchedulersProvider
{
    constructor(
        private readonly maxParallelRequestsToKey: number,
        private readonly extractKey: (modelParams: ResolvedModelParams) => K,
        private readonly constructSchedulerName: (key: K) => string,
        private readonly enableModelsSchedulingDebugLogs: boolean
    ) {}

    private readonly keyToScheduler: Map<K, AsyncScheduler> = new Map();

    getScheduler(modelParams: ResolvedModelParams): AsyncScheduler {
        const key = this.extractKey(modelParams);
        return getOrPut(
            this.keyToScheduler,
            key,
            () =>
                new AsyncScheduler(
                    this.maxParallelRequestsToKey,
                    this.enableModelsSchedulingDebugLogs,
                    this.constructSchedulerName(key)
                )
        );
    }
}

/**
 * Maintains a separate `AsyncScheduler` per model id, each limiting parallelism by `1`.
 * Effectively, that means generation parallelism is unlimited.
 */
export class UnlimitedSchedulersProvider<
    ResolvedModelParams extends ModelParams,
> implements SchedulersProvider
{
    constructor(
        private readonly schedulerName: string,
        private readonly enableModelsSchedulingDebugLogs: boolean
    ) {}

    private readonly modelIdToScheduler: Map<string, AsyncScheduler> =
        new Map();

    getScheduler(modelParams: ResolvedModelParams): AsyncScheduler {
        return getOrPut(
            this.modelIdToScheduler,
            modelParams.modelId,
            () =>
                new AsyncScheduler(
                    1,
                    this.enableModelsSchedulingDebugLogs,
                    this.schedulerName
                )
        );
    }
}

/**
 * Maintains a single `AsyncScheduler`, limiting parallelism globally.
 */
export class LimitedParallelismSchedulersProvider
    implements SchedulersProvider
{
    constructor(
        private readonly maxParallelRequests: number,
        private readonly schedulerName: string,
        private readonly enableModelsSchedulingDebugLogs: boolean
    ) {}

    private readonly scheduler = new AsyncScheduler(
        this.maxParallelRequests,
        this.enableModelsSchedulingDebugLogs,
        this.schedulerName
    );

    getScheduler(_modelParams: ModelParams): AsyncScheduler {
        return this.scheduler;
    }
}

export namespace SchedulersProviderBuilders {
    /**
     * Limits parallelism to the service for the models with the same key (extracted by `extractKey`).
     */
    export function limitParallelismForModelsWithSameKey<
        ResolvedModelParams extends ModelParams,
        K,
    >(
        maxParallelRequestsToKey: number,
        extractKey: (modelParams: ResolvedModelParams) => K,
        serviceFullName: string,
        enableModelsSchedulingDebugLogs: boolean
    ): LimitedByKeyParallelismSchedulersProvider<ResolvedModelParams, K> {
        return new LimitedByKeyParallelismSchedulersProvider<
            ResolvedModelParams,
            K
        >(
            maxParallelRequestsToKey,
            extractKey,
            (key) =>
                `Models Scheduler: ${serviceFullName}, "${key}" / max ${maxParallelRequestsToKey} requests in parallel`,
            enableModelsSchedulingDebugLogs
        );
    }

    /**
     * Limits parallelism to the service for the models with the same `modelId`.
     * Effectively, parallelism is unlimited.
     */
    export function unlimitedParallelism<
        ResolvedModelParams extends ModelParams,
    >(serviceFullName: string, enableModelsSchedulingDebugLogs: boolean) {
        return new UnlimitedSchedulersProvider<ResolvedModelParams>(
            `Models Scheduler: ${serviceFullName} Service, unlimited parallelism`,
            enableModelsSchedulingDebugLogs
        );
    }

    /**
     * Limit parallelism to the service globally, regardless of the models involved.
     */
    export function limitParallelismGlobally(
        maxParallelRequests: number,
        serviceFullName: string,
        enableModelsSchedulingDebugLogs: boolean
    ) {
        return new LimitedParallelismSchedulersProvider(
            maxParallelRequests,
            `Models Scheduler: ${serviceFullName} Service, max ${maxParallelRequests} request per time`,
            enableModelsSchedulingDebugLogs
        );
    }
}
