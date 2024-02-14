import { 
    RequestType,
    BaseLanguageClient,
    Position,
    DocumentUri,
    VersionedTextDocumentIdentifier,
    Diagnostic,
    ProtocolNotificationType, 
    Disposable,
    TextDocumentIdentifier
} from 'vscode-languageclient';

import {
    DidCloseTextDocumentNotification,
    DidCloseTextDocumentParams,
    DidOpenTextDocumentParams,
    DidOpenTextDocumentNotification,
    LogTraceNotification, 
    PublishDiagnosticsNotification
} from 'vscode-languageclient';

import { 
    GoalRequest, 
    GoalAnswer, 
    PpString, 
    Goal
} from "../lib/types";

import { readFileSync } from 'fs';
import { sleep } from '../utils/general';

import { 
    CoqLspServerConfig, 
    CoqLspClientConfig 
} from './coqLspConfig';

import { CoqLspConnector } from './coqLspConnector';
import { Mutex } from "async-mutex";

import { 
    FlecheDocument,
    FlecheDocumentParams
} from './coqLspTypes';

import { 
    CoqLspError
} from './coqLspTypes';

export interface CoqLspClientInterface extends Disposable {
    getFirstGoalAtPoint(
        position: Position, 
        documentUri: DocumentUri,
        version: number, 
        pretac: string
    ): Promise<Goal<PpString> | Error>

    openTextDocument(uri: DocumentUri, version: number): Promise<void>

    closeTextDocument(uri: DocumentUri): Promise<void>

    openAndGetFlecheDocument(uri: DocumentUri): Promise<FlecheDocument>
}

const goalReqType = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
    "proof/goals"
);

const flecheDocReqType = new RequestType<FlecheDocumentParams, FlecheDocument, void>(
    "coq/getDocument"
);

export class CoqLspClient implements CoqLspClientInterface {
    private client: BaseLanguageClient;
    private subscriptions: Disposable[] = [];
    private mutex = new Mutex();

    constructor(
        serverConfig: CoqLspServerConfig,
        clientConfig: CoqLspClientConfig,
    ) {
        this.client = new CoqLspConnector(serverConfig, clientConfig);
    }

    async getFirstGoalAtPoint(
        position: Position, 
        documentUri: DocumentUri,
        version: number, 
        pretac?: string
    ): Promise<Goal<PpString> | Error> {
        return await this.mutex.runExclusive(async () => {
            return this.getFirstGoalAtPointUnsafe(position, documentUri, version, pretac);
        });
    }

    async openTextDocument(uri: DocumentUri, version: number = 1): Promise<void> {
        return await this.mutex.runExclusive(async () => {
            return this.openTextDocumentUnsafe(uri, version);
        });
    }

    async closeTextDocument(uri: DocumentUri): Promise<void> {
        return await this.mutex.runExclusive(async () => {
            return this.closeTextDocumentUnsafe(uri);
        });
    }

    async openAndGetFlecheDocument(uri: DocumentUri): Promise<FlecheDocument> {
        return await this.mutex.runExclusive(async () => {
            return this.openAndGetFlecheDocumentUnsafe(uri);
        });
    }

    private async getFirstGoalAtPointUnsafe(
        position: Position, 
        documentUri: DocumentUri,
        version: number, 
        pretac?: string
    ): Promise<Goal<PpString> | Error> {
        let goalRequestParams: GoalRequest = {
            textDocument: VersionedTextDocumentIdentifier.create(
                documentUri,
                version
            ),
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
        };

        if (pretac) {
            goalRequestParams.pretac = pretac;
        }

        const goals = await this.client.sendRequest(goalReqType, goalRequestParams);
        
        const goal = goals?.goals?.goals?.shift() ?? undefined;
        if (!goal) {
            return new CoqLspError("No goals at point.");
        }

        return goal;
    }

    private async waitUntilOpened(
        requestType: ProtocolNotificationType<any, any>,
        params: any, 
        uri: DocumentUri,
        timeout: number = 50000,
    ): Promise<Diagnostic[]> {
        await this.client.sendNotification(requestType, params);

        let pendingProgress = true;
        let pendingDiagnostic = true;
        let awaitedDiagnostic = null;

        this.subscriptions.push(this.client.onNotification(LogTraceNotification.type, (params) => {
            if (params.message.includes("document fully checked")) {
                pendingProgress = false;
            }
        })); 

        this.subscriptions.push(this.client.onNotification(PublishDiagnosticsNotification.type, (params) => {
            if (params.uri.toString() === uri.toString()) {
                pendingDiagnostic = false;
                awaitedDiagnostic = params.diagnostics;
            }
        }));

        while (timeout > 0 && (pendingProgress || pendingDiagnostic)) {
            await sleep(100);
            timeout -= 100;
        }

        if (
            timeout <= 0 ||
            pendingProgress || 
            pendingDiagnostic || 
            awaitedDiagnostic === null
        ) {
            throw new Error("Coq-lsp did not respond in time");
        }

        return awaitedDiagnostic;
    }

    private async openTextDocumentUnsafe(uri: DocumentUri, version: number = 1): Promise<void> {
        const docText = readFileSync(uri).toString();

        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: uri.toString(),
                languageId: "coq",
                version: version,
                text: docText
            }
        };

        await this.waitUntilOpened(DidOpenTextDocumentNotification.type, params, uri);
    }

    private async closeTextDocumentUnsafe(uri: DocumentUri): Promise<void> {
        const params: DidCloseTextDocumentParams = {
            textDocument: {
                uri: uri,
            }
        };

        await this.client.sendNotification(DidCloseTextDocumentNotification.type, params);
    }

    private async openAndGetFlecheDocumentUnsafe(uri: DocumentUri): Promise<FlecheDocument> {
        this.openTextDocumentUnsafe(uri);
        let textDocument = TextDocumentIdentifier.create(uri);
        let params: FlecheDocumentParams = { textDocument };
        const doc = await this.client.sendRequest(flecheDocReqType, params);
        
        return doc;
    }

    dispose(): void {
        this.subscriptions.forEach((d) => d.dispose());
    }
}