import { TestCoqLspClientOptions } from "../coqLspBuilders";
import {
    CoqLspClient,
    DiagnosticMessage,
    OpenDocumentSpec,
} from "../coqLspClient";

/**
 * Manages creation and scheduling of `CoqLspClient` instances
 * to limit the resources being consumed between the callers.
 * Namely, the resource to be limited is the number of `coq-lsp` server processes
 * that are created one per each `CoqLspClient`.
 */
export abstract class CoqLspProvider {
    abstract withCoqLspClient<T>(
        options: TestCoqLspClientOptions,
        block: (coqLspClient: CoqLspClient) => Promise<T>
    ): Promise<T>;

    async withDocumentOpenedByTestCoqLsp<T>(
        openDocumentSpec: OpenDocumentSpec,
        options: TestCoqLspClientOptions,
        block: (
            coqLspClient: CoqLspClient,
            openedDocDiagnostic: DiagnosticMessage
        ) => Promise<T>
    ): Promise<T> {
        return this.withCoqLspClient<T>(options, (coqLspClient) =>
            coqLspClient.withTextDocument(
                openDocumentSpec,
                (openedDocDiagnostic) =>
                    block(coqLspClient, openedDocDiagnostic)
            )
        );
    }

    async dispose() {}
}
