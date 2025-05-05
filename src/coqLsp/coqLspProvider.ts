import { AsyncScheduler } from "../utils/async/asyncScheduler";

import {
    TestCoqLspClientOptions,
    withTestCoqLspClient,
} from "./coqLspBuilders";
import { CoqLspClient } from "./coqLspClient";

/**
 * Manages creation and scheduling of `CoqLspClient` instances
 * to limit the resources being consumed between the callers.
 * Namely, the resource to be limited is the number of `coq-lsp` server processes
 * that are created one per each `CoqLspClient`.
 */
export interface CoqLspProvider {
    withCoqLspClient<T>(
        options: TestCoqLspClientOptions,
        block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T>;
}

export class UnlimitedParallelismCoqLspProvider implements CoqLspProvider {
    async withCoqLspClient<T>(
        options: TestCoqLspClientOptions,
        block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T> {
        return withTestCoqLspClient(options, block);
    }
}

export class LimitedParallelismCoqLspProvider implements CoqLspProvider {
    private readonly scheduler: AsyncScheduler;
    private readonly onSchedulingLog: (message: string) => void;

    constructor(
        maxRunningClients: number,
        onSchedulingLog?: (message: string) => void
    ) {
        this.scheduler = new AsyncScheduler(
            maxRunningClients,
            onSchedulingLog !== undefined,
            "limited `coq-lsp` clients scheduler"
        );
        this.onSchedulingLog = onSchedulingLog ?? (() => {});
    }

    async withCoqLspClient<T>(
        options: TestCoqLspClientOptions,
        block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T> {
        return this.scheduler.scheduleTask(
            () => withTestCoqLspClient(options, block),
            this.onSchedulingLog
        );
    }
}

export namespace CoqLspProviders {
    const unlimitedProvider = new UnlimitedParallelismCoqLspProvider();

    export function newCoqLspPerRequest(): UnlimitedParallelismCoqLspProvider {
        return unlimitedProvider;
    }

    export function newCoqLspPerRequestWithLimitedParallelism(
        maxRunningClients: number
    ): LimitedParallelismCoqLspProvider {
        return new LimitedParallelismCoqLspProvider(maxRunningClients);
    }

    // TODO: implement one that
    // - reuses existing clients (& recreates on failure), maybe by workspace/file hint
    // - limits max parallel requests per one
}
