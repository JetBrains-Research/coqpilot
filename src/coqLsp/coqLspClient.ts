import { Mutex } from "async-mutex";
import { readFileSync } from "fs";
import { Err, Ok, Result } from "ts-results";
import { OutputChannel } from "vscode";
import {
    BaseLanguageClient,
    Diagnostic,
    DidCloseTextDocumentNotification,
    DidCloseTextDocumentParams,
    DidOpenTextDocumentNotification,
    DidOpenTextDocumentParams,
    Disposable,
    LogTraceNotification,
    Position,
    ProtocolNotificationType,
    PublishDiagnosticsNotification,
    PublishDiagnosticsParams,
    RequestType,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
} from "vscode-languageclient";

import { throwOnAbort } from "../core/abortUtils";

import { EventLogger } from "../logging/eventLogger";
import { Uri } from "../utils/uri";

import { CoqLspClientConfig, CoqLspServerConfig } from "./coqLspConfig";
import { CoqLspConnector } from "./coqLspConnector";
import {
    CoqLspError,
    CoqLspStartupError,
    FlecheDocument,
    FlecheDocumentParams,
    GoalAnswer,
    GoalRequest,
    PpString,
    ProofGoal,
} from "./coqLspTypes";

export interface DocumentSpec {
    uri: Uri;
    version?: number;
}

export interface CoqLspClient extends Disposable {
    /**
     * Fetches all goals present at the given position in the document.
     * This method doesn't open the document implicitly, therefore
     * it assumes that openTextDocument has been called before.
     * @param position Position in the document where to fetch the goals
     * @param documentUri Uri of the document
     * @param version Version of the document
     * @param command Optional command to execute before fetching the goals
     * @returns All goals present at the given position, not only the first one
     */
    getGoalsAtPoint(
        position: Position,
        documentUri: Uri,
        version: number,
        command?: string
    ): Promise<Result<ProofGoal[], Error>>;

    /**
     * The wrapper for the `getGoalsAtPoint` method returning only the first goal of the extracted ones.
     * If the goals extraction is not successfull, this method will throw a `CoqLspError`.
     */
    getFirstGoalAtPointOrThrow(
        position: Position,
        documentUri: Uri,
        version: number,
        command?: string
    ): Promise<ProofGoal>;

    /**
     * Returns a FlecheDocument for the given uri.
     * This method doesn't open the document implicitly, therefore
     * it assumes that openTextDocument has been called before.
     */
    getFlecheDocument(uri: Uri): Promise<FlecheDocument>;

    openTextDocument(uri: Uri, version?: number): Promise<DiagnosticMessage>;

    closeTextDocument(uri: Uri): Promise<void>;

    withTextDocument<T>(
        documentSpec: DocumentSpec,
        block: (openedDocDiagnostic: DiagnosticMessage) => Promise<T>
    ): Promise<T>;
}

const goalReqType = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
    "proof/goals"
);

const flecheDocReqType = new RequestType<
    FlecheDocumentParams,
    FlecheDocument,
    void
>("coq/getDocument");

export type DiagnosticMessage = string | undefined;

export class CoqLspClientImpl implements CoqLspClient {
    private client: BaseLanguageClient;
    private subscriptions: Disposable[] = [];
    private mutex = new Mutex();

    private constructor(
        coqLspConnector: CoqLspConnector,
        public readonly eventLogger?: EventLogger,
        public readonly abortSignal?: AbortSignal
    ) {
        this.client = coqLspConnector;
        this.trackSuspiciousLspErrors();
    }

    static async create(
        serverConfig: CoqLspServerConfig,
        clientConfig: CoqLspClientConfig,
        logOutputChannel: OutputChannel,
        eventLogger?: EventLogger,
        abortSignal?: AbortSignal
    ): Promise<CoqLspClientImpl> {
        const connector = new CoqLspConnector(
            serverConfig,
            clientConfig,
            logOutputChannel,
            eventLogger
        );
        await connector.start().catch((error) => {
            throw new CoqLspStartupError(
                `failed to start coq-lsp with Error: ${error.message}`,
                clientConfig.coq_lsp_server_path
            );
        });
        return new CoqLspClientImpl(connector, eventLogger, abortSignal);
    }

    async getGoalsAtPoint(
        position: Position,
        documentUri: Uri,
        version: number,
        command?: string
    ): Promise<Result<ProofGoal[], Error>> {
        return await this.mutex.runExclusive(async () => {
            throwOnAbort(this.abortSignal);
            return this.getGoalsAtPointUnsafe(
                position,
                documentUri,
                version,
                command
            );
        });
    }

    async getFirstGoalAtPointOrThrow(
        position: Position,
        documentUri: Uri,
        version: number,
        command?: string
    ): Promise<ProofGoal> {
        return await this.mutex.runExclusive(async () => {
            throwOnAbort(this.abortSignal);
            const goals = await this.getGoalsAtPointUnsafe(
                position,
                documentUri,
                version,
                command
            );
            if (goals.err) {
                throw goals.val;
            } else if (goals.val.length === 0) {
                throw new CoqLspError(
                    `Failed to get the first goal: list of goals is empty at the position ${position} of ${documentUri.fsPath}`
                );
            }
            return goals.val[0];
        });
    }

    async openTextDocument(
        uri: Uri,
        version: number = 1
    ): Promise<DiagnosticMessage> {
        return await this.mutex.runExclusive(async () => {
            throwOnAbort(this.abortSignal);
            return this.openTextDocumentUnsafe(uri, version);
        });
    }

    async closeTextDocument(uri: Uri): Promise<void> {
        return await this.mutex.runExclusive(async () => {
            throwOnAbort(this.abortSignal);
            return this.closeTextDocumentUnsafe(uri);
        });
    }

    async withTextDocument<T>(
        documentSpec: DocumentSpec,
        block: (openedDocDiagnostic: DiagnosticMessage) => Promise<T>
    ): Promise<T> {
        const diagnostic = await this.openTextDocument(
            documentSpec.uri,
            documentSpec.version
        );
        // TODO: discuss whether coq-lsp is capable of maintaining several docs opened
        // or we need a common lock for open-close here
        try {
            return await block(diagnostic);
        } finally {
            await this.closeTextDocument(documentSpec.uri);
        }
    }

    async getFlecheDocument(uri: Uri): Promise<FlecheDocument> {
        return await this.mutex.runExclusive(async () => {
            throwOnAbort(this.abortSignal);
            return this.getFlecheDocumentUnsafe(uri);
        });
    }

    /**
     * Dirty due to the fact that the client sends no pure
     * error: https://github.com/ejgallego/coq-lsp/blob/f98b65344c961d1aad1e0c3785199258f21c3abc/controller/request.ml#L29
     */
    cleanLspError(errorMsg?: string): string | undefined {
        const errorMsgPrefixRegex = /^Error in .* request: (.*)$/s;
        if (!errorMsg) {
            return undefined;
        }
        const match = errorMsg.match(errorMsgPrefixRegex);
        return match ? match[1] : undefined;
    }

    removeTraceFromLspError(errorMsgWithTrace: string): string | undefined {
        const traceStartString = "Raised at";

        if (!errorMsgWithTrace.includes(traceStartString)) {
            return errorMsgWithTrace.split("\n").shift();
        }

        return errorMsgWithTrace
            .substring(0, errorMsgWithTrace.indexOf(traceStartString))
            .trim();
    }

    trackSuspiciousLspErrors() {
        this.client.onNotification(PublishDiagnosticsNotification.type, (params: PublishDiagnosticsParams) => {
            function filterIncorrectLspSuspectedDiagnostics(diagnostic: Diagnostic): boolean {
                const errorSubstrings = [
                    "Cannot find a physical path bound to logical path",
                    "Dynlink error: error loading shared library"
                ]

                return errorSubstrings.some((substr) => diagnostic.message.includes(substr) && diagnostic.severity === 1);
            }

            const suspectedDiagnostics = params.diagnostics.filter(filterIncorrectLspSuspectedDiagnostics);
            if (suspectedDiagnostics.length > 0) { 
                const data = {
                    uri: params.uri.toString(),
                    version: params.version,
                    diagnosticMessage: suspectedDiagnostics.map((d) => d.message)
                }
                const firstErrorMessage = suspectedDiagnostics[0].message.split("\n")[0];
    
                this.eventLogger?.log(CoqLspConnector.wrongServerSuspectedEvent, firstErrorMessage, data);
            }
        });
    }

    filterDiagnostics(
        diagnostics: Diagnostic[],
        position: Position
    ): string | undefined {
        const diagnosticMessageWithTrace = diagnostics
            .filter((diag) => diag.range.start.line >= position.line)
            .filter((diag) => diag.severity === 1) // 1 is error
            .shift()?.message;

        if (!diagnosticMessageWithTrace) {
            return undefined;
        } else {
            return this.removeTraceFromLspError(diagnosticMessageWithTrace);
        }
    }

    private async getGoalsAtPointUnsafe(
        position: Position,
        documentUri: Uri,
        version: number,
        command?: string
    ): Promise<Result<ProofGoal[], Error>> {
        let goalRequestParams: GoalRequest = {
            textDocument: VersionedTextDocumentIdentifier.create(
                documentUri.uri,
                version
            ),
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
            command: command,
        };

        try {
            const goalAnswer = await this.client.sendRequest(
                goalReqType,
                goalRequestParams
            );
            const goals = goalAnswer?.goals?.goals;

            if (!goals) {
                return Err(CoqLspError.unknownError());
            }

            return Ok(goals);
        } catch (e) {
            if (e instanceof Error) {
                const errorMsg = this.cleanLspError(
                    this.removeTraceFromLspError(e.message)
                );
                if (errorMsg) {
                    return Err(new CoqLspError(errorMsg));
                }
                return Err(
                    new CoqLspError(
                        "Unable to parse CoqLSP error, please report this issue: " +
                            e.message
                    )
                );
            }

            return Err(CoqLspError.unknownError());
        }
    }

    private sleep(ms: number): Promise<ReturnType<typeof setTimeout>> {
        return new Promise((resolve) => setTimeout(resolve, ms));
    }

    private async waitUntilFileFullyChecked(
        requestType: ProtocolNotificationType<any, any>,
        params: any,
        uri: Uri,
        version: number,
        lastDocumentEndPosition?: Position,
        timeout: number = 300000
    ): Promise<DiagnosticMessage> {
        await this.client.sendNotification(requestType, params);

        let pendingProgress = true;
        let pendingDiagnostic = true;
        let awaitedDiagnostics: Diagnostic[] | undefined = undefined;

        this.subscriptions.push(
            this.client.onNotification(LogTraceNotification.type, (params) => {
                if (params.message.includes("document fully checked")) {
                    pendingProgress = false;
                }
            })
        );

        this.subscriptions.push(
            this.client.onNotification(
                PublishDiagnosticsNotification.type,
                (params) => {
                    if (
                        params.uri.toString() === uri.uri &&
                        params.version === version
                    ) {
                        pendingDiagnostic = false;
                        awaitedDiagnostics = params.diagnostics;

                        if (
                            lastDocumentEndPosition &&
                            this.filterDiagnostics(
                                params.diagnostics,
                                lastDocumentEndPosition
                            ) !== undefined
                        ) {
                            pendingProgress = false;
                        }
                    }
                }
            )
        );

        while (timeout > 0 && (pendingProgress || pendingDiagnostic)) {
            await this.sleep(100);
            timeout -= 100;
        }

        if (
            timeout <= 0 ||
            pendingProgress ||
            pendingDiagnostic ||
            awaitedDiagnostics === undefined
        ) {
            throw new CoqLspError("coq-lsp did not respond in time");
        }

        this.subscriptions.forEach((d) => d.dispose());

        return this.filterDiagnostics(
            awaitedDiagnostics,
            lastDocumentEndPosition ?? Position.create(0, 0)
        );
    }

    private async openTextDocumentUnsafe(
        uri: Uri,
        version: number = 1
    ): Promise<DiagnosticMessage> {
        const docText = readFileSync(uri.fsPath).toString();

        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: uri.uri,
                languageId: "coq",
                version: version,
                text: docText,
            },
        };

        return await this.waitUntilFileFullyChecked(
            DidOpenTextDocumentNotification.type,
            params,
            uri,
            version
        );
    }

    private async closeTextDocumentUnsafe(uri: Uri): Promise<void> {
        const params: DidCloseTextDocumentParams = {
            textDocument: {
                uri: uri.uri,
            },
        };

        await this.client.sendNotification(
            DidCloseTextDocumentNotification.type,
            params
        );
    }

    private async getFlecheDocumentUnsafe(uri: Uri): Promise<FlecheDocument> {
        let textDocument = TextDocumentIdentifier.create(uri.uri);
        let params: FlecheDocumentParams = { textDocument };
        const doc = await this.client.sendRequest(flecheDocReqType, params);

        return doc;
    }

    /**
     * _Implementation note:_ although this `dispose` implementation calls an async method,
     * we are not tend to await it, as well as `CoqLspClient.dispose()` in general.
     *
     * Since different coq-lsp clients correspond to different processes,
     * they don't have any shared resources; therefore, a new client can be started without
     * waiting for the previous one to finish. Thus, we don't await for this `dispose()` call
     * to finish, the client and its process will be disposed at some point asynchronously.
     */
    dispose(): void {
        this.subscriptions.forEach((d) => d.dispose());
        this.client.stop();
    }
}
