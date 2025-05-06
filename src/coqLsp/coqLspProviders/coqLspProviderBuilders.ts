import { CoqLspProvider } from "./abstractCoqLspProvider";
import {
    LimitedParallelismCoqLspProvider,
    UnlimitedParallelismCoqLspProvider,
} from "./newClientPerRequestProviders";
import { ReusableFileScopeCoqLspClients } from "./reusableFileScopeClientsProvider";

export type CoqLspProviderBuilder = () => CoqLspProvider;

export namespace CoqLspProviderBuilders {
    const unlimitedProvider = new UnlimitedParallelismCoqLspProvider();

    /**
     * Provides stateless implementation of creating new `coq-lsp` per request.
     *
     * The resulted `CoqLspProvider` is not needed to be disposed
     * (and could not been disposed, its `dispose` method does nothing).
     */
    export function newClientPerRequest(): CoqLspProviderBuilder {
        return () => unlimitedProvider;
    }

    /**
     * Provides stateless implementation of creating new `coq-lsp` per request
     * with limited number of clients running in parallel.
     *
     * The resulted `CoqLspProvider` is not needed to be disposed
     * (and could not been disposed, its `dispose` method does nothing).
     */
    export function newClientPerRequestWithLimitedParallelism(
        maxRunningClients: number,
        onSchedulingLog?: (message: string) => void
    ): CoqLspProviderBuilder {
        return () =>
            new LimitedParallelismCoqLspProvider(
                maxRunningClients,
                onSchedulingLog
            );
    }

    // TODO: document
    export function reusableFileScopeClients(
        maxRunningClients: number,
        onSchedulingLog?: (message: string) => void
    ): CoqLspProviderBuilder {
        return () =>
            new ReusableFileScopeCoqLspClients(
                maxRunningClients,
                onSchedulingLog
            );
    }
}
