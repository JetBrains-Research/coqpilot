import { Disposable, OutputChannel } from "vscode";

import { createCoqLspClient } from "../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../coqLsp/coqLspClient";

import { CompletionAbortError } from "../core/abortUtils";

import { EventLogger, Severity } from "../logging/eventLogger";

import { parseCoqLspServerPath } from "./settings/configReaders";
import { PluginStatusIndicator } from "./ui/pluginStatusIndicator";
import { CoqLspConnector } from "../coqLsp/coqLspConnector";
import { EditorMessages, showMessageToUser } from "./ui/messages/editorMessages";

export class SessionState implements Disposable {
    private _isActive = true;
    private _coqLspClient: CoqLspClient;
    private _abortController: AbortController;

    // When user triggers abort for completions
    // and there are multiple completions in progress,
    // we want to notify the user only once.
    private _userNotifiedAboutAbort = false;

    throwOnInactiveSession(): void {
        if (!this._isActive) {
            throw new Error("Trying to access a disposed session state");
        }
    }

    get isActive(): boolean {
        return this._isActive;
    }

    get userNotifiedAboutAbort(): boolean {
        return this._userNotifiedAboutAbort;
    }

    get coqLspClient(): CoqLspClient {
        this.throwOnInactiveSession();
        return this._coqLspClient;
    }

    get abortController(): AbortController {
        this.throwOnInactiveSession();
        return this._abortController;
    }

    private constructor(
        coqLspClient: CoqLspClient,
        abortController: AbortController,
        private readonly logOutputChannel: OutputChannel,
        private readonly eventLogger: EventLogger,
        private readonly pluginStatusIndicator: PluginStatusIndicator
    ) {
        this._coqLspClient = coqLspClient;
        this._abortController = abortController;

        this.eventLogger.log("session-start", "User has started a new session");
    }

    static async create(
        logOutputChannel: OutputChannel,
        eventLogger: EventLogger,
        pluginStatusIndicator: PluginStatusIndicator
    ): Promise<SessionState> {
        const abortController = new AbortController();
        const coqLspServerPath = parseCoqLspServerPath();

        eventLogger.subscribe(
            CoqLspConnector.wrongServerSuspectedEvent,
            Severity.INFO,
            (message, _) => {
                showMessageToUser(
                    EditorMessages.wrongCoqLspSuspected(
                        coqLspServerPath,
                        message
                    ),
                    "error"
                );
            }
        );

        const coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            logOutputChannel,
            eventLogger,
            abortController.signal
        );

        pluginStatusIndicator.updateStatusBar(true);

        return new SessionState(
            coqLspClient,
            abortController,
            logOutputChannel,
            eventLogger,
            pluginStatusIndicator
        );
    }

    markAbortNotificationAsShown(): void {
        this._userNotifiedAboutAbort = true;
    }

    showInProgressSpinner(): void {
        this.pluginStatusIndicator.showInProgressSpinner();
    }

    hideInProgressSpinner(): void {
        this.pluginStatusIndicator.hideInProgressSpinner(this._isActive);
    }

    async toggleCurrentSession(): Promise<void> {
        if (this._isActive) {
            this.abort();
        } else {
            await this.restartSession();
        }
    }

    private abort(): void {
        this._isActive = false;
        this._abortController.abort(new CompletionAbortError());
        this._coqLspClient.dispose();

        this.pluginStatusIndicator.updateStatusBar(this._isActive);

        this.eventLogger.log(
            "session-abort",
            "User has triggered a session abort: Stopping all completions"
        );
    }

    private async restartSession(): Promise<void> {
        this._isActive = true;
        this._abortController = new AbortController();
        this._userNotifiedAboutAbort = false;

        const coqLspServerPath = parseCoqLspServerPath();
        this._coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            this.logOutputChannel,
            this.eventLogger,
            this._abortController.signal
        );

        this.pluginStatusIndicator.updateStatusBar(this._isActive);

        this.eventLogger.log(
            "session-restart",
            "User has restarted the session"
        );
    }

    dispose(): void {
        this._coqLspClient.dispose();
    }
}
