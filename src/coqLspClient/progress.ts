import { Disposable, Range } from "vscode";

import {
  NotificationType,
  VersionedTextDocumentIdentifier,
  BaseLanguageClient
} from "vscode-languageclient";

import { ProgressBar } from "../extension/progressBar";

/* eslint-disable @typescript-eslint/naming-convention */
enum CoqFileProgressKind {
    Processing = 1,
    FatalError = 2,
}
/* eslint-enable @typescript-eslint/naming-convention */

interface CoqFileProgressProcessingInfo {
    /** Range for which the processing info was reported. */
    range: Range;
    /** Kind of progress that was reported. */
    kind?: CoqFileProgressKind;
}

interface CoqFileProgressParams {
    /** The text document to which this progress notification applies. */
    textDocument: VersionedTextDocumentIdentifier;

    /**
     * Array containing the parts of the file which are still being processed.
     * The array should be empty if and only if the server is finished processing.
     */
    processing: CoqFileProgressProcessingInfo[];
}

const coqFileProgress = new NotificationType<CoqFileProgressParams>(
    "$/coq/fileProgress"
);

export class FileProgressManager {
    private fileProgress: Disposable;
    private progressBar: ProgressBar;

    constructor(client: BaseLanguageClient, progressBar: ProgressBar) {
        this.progressBar = progressBar;
        this.fileProgress = client.onNotification(coqFileProgress, (params) => {
            if (params.processing.length === 0) {
                return;
            }

            if (!this.progressBar.isInitialized || this.progressBar.identifier !== params.textDocument.uri) {
                return;
            }

            const range = params.processing
                .map((fp) => client.protocol2CodeConverter.asRange(fp.range))
                .filter((r) => !r.isEmpty)
                .shift();
            
            if (range === undefined) {
                return;
            }

            this.progressBar.updateCount(range.start.line);
        });   
    }

    subscribeForUpdates(uri: string, total: number) {
        this.progressBar.initialize(total, uri);
    }

    stopListening() {
        this.progressBar.finish();
    }

    dispose() {
        this.fileProgress.dispose();
    }
}