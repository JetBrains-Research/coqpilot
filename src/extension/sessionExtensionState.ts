import { Disposable, OutputChannel } from "vscode";

import { createCoqLspClient } from "../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../coqLsp/coqLspClient";

import { EventLogger } from "../logging/eventLogger";

import { parseCoqLspServerPath } from "./configReaders";
import { CompletionAbortError } from "./extensionAbortUtils";

export class SessionExtensionState implements Disposable {
    private constructor(
        readonly coqLspClient: CoqLspClient,
        readonly abortController: AbortController
    ) {}

    static async create(
        logOutputChannel: OutputChannel,
        eventLogger: EventLogger
    ): Promise<SessionExtensionState> {
        const abortController = new AbortController();
        const coqLspServerPath = parseCoqLspServerPath();

        const coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            logOutputChannel,
            eventLogger,
            abortController
        );

        return new SessionExtensionState(coqLspClient, abortController);
    }

    abort(): void {
        this.abortController.abort(new CompletionAbortError());
    }

    dispose(): void {
        this.abortController.abort();
        this.coqLspClient.dispose();
    }
}
