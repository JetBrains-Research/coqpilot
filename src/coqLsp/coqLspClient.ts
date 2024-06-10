import { Mutex } from "async-mutex";
import { readFileSync } from "fs";
import {
    BaseLanguageClient,
    Diagnostic,
    Disposable,
    Position,
    ProtocolNotificationType,
    RequestType,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import {
    DidChangeTextDocumentNotification,
    DidChangeTextDocumentParams,
    DidCloseTextDocumentNotification,
    DidCloseTextDocumentParams,
    DidOpenTextDocumentNotification,
    DidOpenTextDocumentParams,
    LogTraceNotification,
    PublishDiagnosticsNotification,
} from "vscode-languageclient";

import { Uri } from "../utils/uri";

import { CoqLspClientConfig, CoqLspServerConfig } from "./coqLspConfig";
import { CoqLspConnector } from "./coqLspConnector";
import { Goal, GoalAnswer, GoalRequest, PpString } from "./coqLspTypes";
import { FlecheDocument, FlecheDocumentParams } from "./coqLspTypes";
import { CoqLspError } from "./coqLspTypes";

export interface CoqLspClientInterface extends Disposable {
    getFirstGoalAtPoint(
        position: Position,
        documentUri: Uri,
        version: number,
        pretac: string
    ): Promise<Goal<PpString> | Error>;

    openTextDocument(uri: Uri, version: number): Promise<DiagnosticMessage>;

    updateTextDocument(
        oldDocumentText: string[],
        appendedSuffix: string,
        uri: Uri,
        version: number
    ): Promise<DiagnosticMessage>;

    closeTextDocument(uri: Uri): Promise<void>;

    getFlecheDocument(uri: Uri): Promise<FlecheDocument>;
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

export class CoqLspClient implements CoqLspClientInterface {
    private client: BaseLanguageClient;
    private subscriptions: Disposable[] = [];
    private mutex = new Mutex();

    constructor(
        serverConfig: CoqLspServerConfig,
        clientConfig: CoqLspClientConfig
    ) {
        this.client = new CoqLspConnector(serverConfig, clientConfig);
        this.client.start();
    }

    async getFirstGoalAtPoint(
        position: Position,
        documentUri: Uri,
        version: number,
        pretac?: string
    ): Promise<Goal<PpString> | Error> {
        return await this.mutex.runExclusive(async () => {
            return this.getFirstGoalAtPointUnsafe(
                position,
                documentUri,
                version,
                pretac
            );
        });
    }

    async openTextDocument(
        uri: Uri,
        version: number = 1
    ): Promise<DiagnosticMessage> {
        return await this.mutex.runExclusive(async () => {
            return this.openTextDocumentUnsafe(uri, version);
        });
    }

    async updateTextDocument(
        oldDocumentText: string[],
        appendedSuffix: string,
        uri: Uri,
        version: number = 1
    ): Promise<DiagnosticMessage> {
        return await this.mutex.runExclusive(async () => {
            return this.updateTextDocumentUnsafe(
                oldDocumentText,
                appendedSuffix,
                uri,
                version
            );
        });
    }

    async closeTextDocument(uri: Uri): Promise<void> {
        return await this.mutex.runExclusive(async () => {
            return this.closeTextDocumentUnsafe(uri);
        });
    }

    async getFlecheDocument(uri: Uri): Promise<FlecheDocument> {
        return await this.mutex.runExclusive(async () => {
            return this.getFlecheDocumentUnsafe(uri);
        });
    }

    filterDiagnostics(
        diagnostics: Diagnostic[],
        position: Position
    ): string | undefined {
        const traceStartString = "Raised at";
        const diagnosticMessageWithTrace = diagnostics
            .filter((diag) => diag.range.start.line >= position.line)
            .filter((diag) => diag.severity === 1) // 1 is error
            .shift()?.message;

        if (!diagnosticMessageWithTrace) {
            return undefined;
        } else if (!diagnosticMessageWithTrace.includes(traceStartString)) {
            return diagnosticMessageWithTrace.split("\n").shift();
        }
        return diagnosticMessageWithTrace
            .substring(0, diagnosticMessageWithTrace.indexOf(traceStartString))
            .trim();
    }

    private async getFirstGoalAtPointUnsafe(
        position: Position,
        documentUri: Uri,
        version: number,
        pretac?: string
    ): Promise<Goal<PpString> | Error> {
        let goalRequestParams: GoalRequest = {
            textDocument: VersionedTextDocumentIdentifier.create(
                documentUri.uri,
                version
            ),
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
        };

        if (pretac) {
            goalRequestParams.pretac = pretac;
        }

        const goals = await this.client.sendRequest(
            goalReqType,
            goalRequestParams
        );
        const goal = goals?.goals?.goals?.shift() ?? undefined;
        if (!goal) {
            return new CoqLspError("no goals at point");
        }

        return goal;
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

    private getTextEndPosition(lines: string[]): Position {
        return Position.create(
            lines.length - 1,
            lines[lines.length - 1].length
        );
    }

    private async updateTextDocumentUnsafe(
        oldDocumentText: string[],
        appendedSuffix: string,
        uri: Uri,
        version: number = 1
    ): Promise<DiagnosticMessage> {
        const updatedText = oldDocumentText.join("\n") + appendedSuffix;
        const oldEndPosition = this.getTextEndPosition(oldDocumentText);

        const params: DidChangeTextDocumentParams = {
            textDocument: {
                uri: uri.uri,
                version: version,
            },
            contentChanges: [
                {
                    text: updatedText,
                },
            ],
        };

        return await this.waitUntilFileFullyChecked(
            DidChangeTextDocumentNotification.type,
            params,
            uri,
            version,
            oldEndPosition
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

    dispose(): void {
        this.subscriptions.forEach((d) => d.dispose());
    }
}
