import {
    window,
    commands,
    ExtensionContext,
    workspace,
    StatusBarAlignment,
    StatusBarItem,
    ThemeColor,
    WorkspaceConfiguration,
} from "vscode";

import {
    BaseLanguageClient,
    LanguageClientOptions,
    RevealOutputChannelOn
} from "vscode-languageclient";

import { CoqLspServerConfig } from "./config";
import { FileProgressManager } from "./progress";
import { ProofView } from "./proofView";

let client: BaseLanguageClient;

let fileProgress: FileProgressManager;
let proofView: ProofView;

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
        let disposable = commands.registerCommand("coqpilot.coqlsp." + command, fn);
        context.subscriptions.push(disposable);
    }

    // Hide files generated to check proofs
    let activationConfig = workspace.getConfiguration();
    let fexc: any = activationConfig.get("files.exclude");
    activationConfig.update("files.exclude", {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        '**/*_cp_aux.v': true,
        ...fexc,
    });

    const stop = () => {
        if (client && client.isRunning()) {
        client
            .dispose(2000)
            .then(updateStatusBar)
            .then(() => {
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

    context.subscriptions.push(proofView);

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

    createEnableButton();

    start();
}

export function deactivateCoqLSP(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}