import { AsyncScheduler } from "../../utils/async/asyncScheduler";
import {
    TestCoqLspClientOptions,
    withTestCoqLspClient,
} from "../coqLspBuilders";
import { CoqLspClient } from "../coqLspClient";

import { CoqLspProvider } from "./abstractCoqLspProvider";

export class UnlimitedParallelismCoqLspProvider extends CoqLspProvider {
    async withCoqLspClient<T>(
        options: TestCoqLspClientOptions,
        block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T> {
        return withTestCoqLspClient(options, block);
    }
}

export class LimitedParallelismCoqLspProvider extends CoqLspProvider {
    private readonly scheduler: AsyncScheduler;
    private readonly onSchedulingLog: (message: string) => void;

    constructor(
        maxRunningClients: number,
        onSchedulingLog?: (message: string) => void
    ) {
        super();
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
