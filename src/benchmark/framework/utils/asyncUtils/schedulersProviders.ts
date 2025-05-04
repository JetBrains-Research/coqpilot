import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { AsyncScheduler } from "../../../../utils/async/asyncScheduler";
import { getOrPut } from "../../../../utils/collectionUtils/mapUtils";
import { LLMServiceStringIdentifier } from "../../structures/common/llmServiceIdentifier";
import { getShortName } from "../commonStructuresUtils/llmServicesUtils";

export interface SchedulersProvider {
    getScheduler(modelParams: ModelParams): AsyncScheduler;
}

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

export function createDefaultLLMServiceSchedulersProvider<
    ResolvedModelParams extends ModelParams,
    K,
>(
    maxParallelRequestsToKey: number,
    extractKey: (modelParams: ResolvedModelParams) => K,
    serviceIdentifier: LLMServiceStringIdentifier,
    enableModelsSchedulingDebugLogs: boolean
): LimitedByKeyParallelismSchedulersProvider<ResolvedModelParams, K> {
    return new LimitedByKeyParallelismSchedulersProvider<
        ResolvedModelParams,
        K
    >(
        maxParallelRequestsToKey,
        extractKey,
        (key) =>
            `Models Scheduler: ${getShortName(serviceIdentifier)} Service, "${key}" / max ${maxParallelRequestsToKey} requests in parallel`,
        enableModelsSchedulingDebugLogs
    );
}

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
