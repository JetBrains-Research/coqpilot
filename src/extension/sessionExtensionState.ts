import { Disposable, OutputChannel } from "vscode";

import { createCoqLspClient } from "../coqLsp/coqLspBuilders";
import { CoqLspClientInterface } from "../coqLsp/coqLspClient";

import { EventLogger } from "../logging/eventLogger";

import { parseCoqLspServerPath } from "./configReaders";
import { CompletionAbortError } from "./extensionAbortUtils";

export class SessionExtensionState implements Disposable {
    public abortController: AbortController = new AbortController();

    private constructor(public readonly coqLspClient: CoqLspClientInterface) {}

    static async create(
        logOutputChannel: OutputChannel,
        eventLogger: EventLogger
    ): Promise<SessionExtensionState> {
        const coqLspServerPath = parseCoqLspServerPath();
        const coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            logOutputChannel,
            eventLogger
        );

        return new SessionExtensionState(coqLspClient);
    }

    abort(): void {
        this.abortController.abort(new CompletionAbortError());
    }

    dispose(): void {
        this.abortController.abort();
        this.coqLspClient.dispose();
    }
}
