import {
    window,
    commands,
    ExtensionContext,
    workspace,
    TextEditor,
    TextEditorSelectionChangeEvent,
    StatusBarAlignment,
    StatusBarItem,
    ThemeColor,
    WorkspaceConfiguration,
} from "vscode";

import {
    BaseLanguageClient,
    LanguageClientOptions,
    RequestType,
    RevealOutputChannelOn,
    VersionedTextDocumentIdentifier,
    NotificationType,
    PublishDiagnosticsParams, 
    LogTraceNotification,
} from "vscode-languageclient";

import {
    FlecheDocumentParams,
    FlecheDocument,
    FlecheSaveParams,
} from "../lib/types";

import { CoqLspServerConfig } from "./config";
import { GoalsManager } from "./goals";
import { FileProgressManager } from "./progress";
import { ProofView } from "./proofView";

let client: BaseLanguageClient;

let goalsManager: GoalsManager;
let fileProgress: FileProgressManager;
let proofView: ProofView;

let pendingOperation: boolean = false;

// Status Bar Button
let lspStatusItem: StatusBarItem;

// Client Factory types
export type ClientFactoryType = (
    context: ExtensionContext,
    clientOptions: LanguageClientOptions,
    wsConfig: WorkspaceConfiguration
) => BaseLanguageClient;

export function activateCoqLSP(
    context: ExtensionContext,
    clientFactory: ClientFactoryType
): void {
    function coqCommand(command: string, fn: () => void) {
        let disposable = commands.registerCommand("coqpilot." + command, fn);
        context.subscriptions.push(disposable);
    }

    function coqEditorCommand(command: string, fn: (editor: TextEditor) => void) {
        let disposable = commands.registerTextEditorCommand(
            "coqpilot." + command,
            fn
        );
        context.subscriptions.push(disposable);
    }

    const stop = () => {
        if (client && client.isRunning()) {
        client
            .dispose(2000)
            .then(updateStatusBar)
            .then(() => {
                goalsManager.dispose();
                fileProgress.dispose();
                proofView.dispose();
            });
        }
    };

    const start = () => {
        if (client && client.isRunning()) { return; }

        const wsConfig = workspace.getConfiguration("coqpilot");
        const initializationOptions = CoqLspServerConfig.create();

        const clientOptions: LanguageClientOptions = {
            documentSelector: [
                { scheme: "file", language: "coq" },
                { scheme: "file", language: "markdown", pattern: "**/*.mv" },
            ],
            outputChannelName: "Coqpilot: coq-lsp events",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions,
            markdown: { isTrusted: true, supportHtml: true },
        };

        let cP = new Promise<BaseLanguageClient>((resolve) => {
            client = clientFactory(context, clientOptions, wsConfig);
            fileProgress = new FileProgressManager(client);
            proofView = new ProofView(client, context);
            resolve(client);
        });

        cP.then((client) =>
            client
                .start()
                .then(updateStatusBar)
                // .then(setListeners)
        ).catch((error) => {
            let emsg = error.toString();
            console.log(`Error in coq-lsp start: ${emsg}`);
            setFailedStatuBar(emsg);
        });
    };

    const restart = () => {
        stop();
        start();
    };

    const toggle = () => {
        if (client && client.isRunning()) {
            stop();
        } else {
            start();
        }
    };

    goalsManager = new GoalsManager();
    context.subscriptions.push(goalsManager);

    const goals = (editor: TextEditor) => {
        if (!client.isRunning()) { return; } 
        let uri = editor.document.uri;
        let version = editor.document.version;
        let position = editor.selection.active;
        console.log(`Goals requested for ${uri} at ${position}`);

        // goalsManager.checkAuxLemma(client, uri, version, position);
    };

    const goalsCall = (
        textEditor: TextEditor,
    ) => {

        if (textEditor.document.languageId !== "coq") {
            return;
        }

        goals(textEditor);
    };

    let goalsHook = window.onDidChangeTextEditorSelection(
        (_evt: TextEditorSelectionChangeEvent) => {
            // console.log("Goals hook activated", evt);
            // goalsCall(evt.textEditor);
            pendingOperation = true;
        }
    );

    context.subscriptions.push(goalsHook);
 
    const saveReq = new RequestType<FlecheDocumentParams, void, void>(
        "coq/saveVo"
    );

    const coqFileDiags = new NotificationType<PublishDiagnosticsParams>(
        "textDocument/publishDiagnostics"
    );

    // const setListeners = () => {
    //     if (client) {
    //         // when any notification is sent to the server from the client, set pendingOperation to true
    //         client.onNotification(LogTraceNotification.type, (params) => {
    //             pendingOperation = false;
    //             if (params.message.includes("document fully checked")) {
    //                 console.log("document fully checked");
    //             }
    //         }); 
    //     }
    // };

    const saveDocument = (editor: TextEditor) => {
        let uri = editor.document.uri;
        let version = editor.document.version;
        let textDocument = VersionedTextDocumentIdentifier.create(
            uri.toString(),
            version
        );
        let params: FlecheSaveParams = { textDocument };
        client
            .sendRequest(saveReq, params)
            .then(() => console.log("document saved", uri.toString()))
            .catch((error) => {
                let errMessage = error.toString();
                console.log(`error in save: ${errMessage}`);
                window.showErrorMessage(errMessage);
            });
    };

    const createEnableButton = () => {
        lspStatusItem = window.createStatusBarItem(
            "coqpilot.enable",
            StatusBarAlignment.Left,
            0
        );
        lspStatusItem.command = "coqpilot.toggle";
        lspStatusItem.text = "coqpilot (activating)";
        lspStatusItem.show();
        context.subscriptions.push(lspStatusItem);
    };

    const updateStatusBar = () => {
        if (client && client.isRunning()) {
            lspStatusItem.text = "$(check) coqpilot";
            lspStatusItem.backgroundColor = undefined;
            lspStatusItem.tooltip = "coqpilot is running. Click to disable.";
        } else {
            lspStatusItem.text = "$(circle-slash) coqpilot (stopped)";
            lspStatusItem.backgroundColor = new ThemeColor(
                "statusBarItem.warningBackground"
            );
            lspStatusItem.tooltip = "coqpilot has been disabled. Click to enable.";
        }
    };

    const setFailedStatuBar = (emsg: string) => {
        lspStatusItem.text = "$(circle-slash) coqpilot (failed to start)";
        lspStatusItem.backgroundColor = new ThemeColor(
            "statusBarItem.errorBackground"
        );
        lspStatusItem.tooltip = `coqpilot couldn't start: ${emsg} Click to retry.`;
    };

    coqCommand("stop", stop);
    coqCommand("start", start);

    coqCommand("restart", restart);
    coqCommand("toggle", toggle);

    coqEditorCommand("go", goals);
    // coqEditorCommand("document", getDocument);
    coqEditorCommand("save", saveDocument);

    createEnableButton();

    start();
}

export function deactivateCoqLSP(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}