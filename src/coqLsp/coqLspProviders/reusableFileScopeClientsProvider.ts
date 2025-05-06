import {
    AsyncLRUCache,
    DisposableItem,
} from "../../benchmark/framework/utils/caching/lruCache";
import { unsupported } from "../../utils/errors/throwErrors";
import { Uri } from "../../utils/structures/uri";
import {
    TestCoqLspClientOptions,
    createTestCoqLspClient,
} from "../coqLspBuilders";
import {
    CoqLspClient,
    DiagnosticMessage,
    OpenDocumentSpec,
} from "../coqLspClient";

import { CoqLspProvider } from "./abstractCoqLspProvider";

class OpenedDocumentCoqLspClient implements DisposableItem {
    constructor(
        readonly client: CoqLspClient,
        readonly openedDocUri: Uri,
        readonly openedDocDiagnostic: DiagnosticMessage
    ) {}

    async dispose() {
        await this.client.closeTextDocument(this.openedDocUri);
        this.client.dispose();
    }
}

export class ReusableFileScopeCoqLspClients extends CoqLspProvider {
    private readonly clientsPool: AsyncLRUCache<OpenedDocumentCoqLspClient>;

    private readonly initializeNewCoqLspClient: (
        openDocumentSpec: OpenDocumentSpec,
        options: TestCoqLspClientOptions
    ) => Promise<OpenedDocumentCoqLspClient>;

    constructor(
        maxRunningClients: number,
        onSchedulingLog?: (message: string) => void
    ) {
        super();
        this.clientsPool = new AsyncLRUCache(
            maxRunningClients,
            onSchedulingLog
        );
        this.initializeNewCoqLspClient = async (
            openDocumentSpec: OpenDocumentSpec,
            options: TestCoqLspClientOptions
        ) => {
            const coqLspClient = await createTestCoqLspClient(options);
            const openedDocDiagnostic = await coqLspClient.openTextDocument(
                openDocumentSpec.uri,
                openDocumentSpec.version,
                openDocumentSpec.timeoutMillis
            );
            return new OpenedDocumentCoqLspClient(
                coqLspClient,
                openDocumentSpec.uri,
                openedDocDiagnostic
            );
        };
    }

    async withCoqLspClient<T>(
        _options: TestCoqLspClientOptions,
        _block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T> {
        unsupported(
            "`ReusableFileScopeCoqLspClients` does not support `withCoqLspClient(...)`, ",
            "it should be used only for `withDocumentOpenedByTestCoqLsp(...)` calls"
        );
    }

    async withDocumentOpenedByTestCoqLsp<T>(
        openDocumentSpec: OpenDocumentSpec,
        options: TestCoqLspClientOptions,
        block: (
            coqLspClient: CoqLspClient,
            openedDocDiagnostic: DiagnosticMessage
        ) => Promise<T>
    ): Promise<T> {
        const filePathKey = openDocumentSpec.uri.fsPath;
        const openedDocClient = await this.clientsPool.getItemByKey(
            filePathKey,
            () => this.initializeNewCoqLspClient(openDocumentSpec, options)
        );
        try {
            return await block(
                openedDocClient.client,
                openedDocClient.openedDocDiagnostic
            );
        } catch (e) {
            await this.clientsPool.removeItemByKey(filePathKey, false);
            throw e;
        }
    }

    async dispose() {
        return this.clientsPool.dispose();
    }
}
