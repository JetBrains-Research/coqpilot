import { Disposable, Range } from "vscode";
import {
  NotificationType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { BaseLanguageClient } from "vscode-languageclient";

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

    constructor(client: BaseLanguageClient) {
        this.fileProgress = client.onNotification(coqFileProgress, (params) => {
            if (params.processing.length === 0) {
                console.log(`Finished processing file ${params.textDocument.uri}`);
                return;
            }
            let ranges = params.processing
                .map((fp) => client.protocol2CodeConverter.asRange(fp.range))
                .filter((r) => !r.isEmpty);
            console.log(`Processing file ${params.textDocument.uri}: ${ranges[0].start.line}-${ranges[0].end.line}`);
        });   
    }

    dispose() {
        this.fileProgress.dispose();
    }
}