import { Disposable, OutputChannel } from "vscode";

import { createCoqLspClient } from "../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../coqLsp/coqLspClient";

import { EventLogger } from "../logging/eventLogger";

import { parseCoqLspServerPath } from "./configReaders";
import { CompletionAbortError } from "./extensionAbortUtils";
import { PluginStatusIndicator } from "./pluginStatusIndicator";

export class SessionState implements Disposable {
    private _isSessionActive = true;
    private _coqLspClient: CoqLspClient;
    private _abortController: AbortController;

    // When user triggers abort for completions
    // and there are multiple completions in progress,
    // we want to notify the user only once.
    private _userNotifiedAboutAbort = false;

    throwOnInactiveSession(): void {
        if (!this._isSessionActive) {
            throw new Error("Trying to access a disposed session state");
        }
    }

    get isSessionActive(): boolean {
        return this._isSessionActive;
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
    }

    static async create(
        logOutputChannel: OutputChannel,
        eventLogger: EventLogger,
        pluginStatusIndicator: PluginStatusIndicator
    ): Promise<SessionState> {
        const abortController = new AbortController();
        const coqLspServerPath = parseCoqLspServerPath();

        const coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            logOutputChannel,
            eventLogger,
            abortController
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

    userReceivedAbortNotification(): void {
        this._userNotifiedAboutAbort = true;
    }

    showInProgressSpinner(): void {
        this.pluginStatusIndicator.showInProgressSpinner();
    }

    hideInProgressSpinner(): void {
        this.pluginStatusIndicator.hideInProgressSpinner(this._isSessionActive);
    }

    async toggleCurrentSession(): Promise<void> {
        if (this._isSessionActive) {
            this.abort();
        } else {
            await this.startNewSession();
        }
    }

    abort(): void {
        this._isSessionActive = false;
        this._abortController.abort(new CompletionAbortError());
        this._coqLspClient.dispose();

        this.pluginStatusIndicator.updateStatusBar(false);

        this.eventLogger.log(
            "session-abort",
            "User has triggered a session abort: Stopping all completions"
        );
    }

    async startNewSession(): Promise<void> {
        this._isSessionActive = true;
        this._abortController = new AbortController();

        const coqLspServerPath = parseCoqLspServerPath();
        this._coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            this.logOutputChannel,
            this.eventLogger,
            this._abortController
        );

        this.pluginStatusIndicator.updateStatusBar(true);

        this.eventLogger.log("session-start", "User has started a new session");
    }

    dispose(): void {
        this._abortController.abort();
        this._coqLspClient.dispose();
    }
}
