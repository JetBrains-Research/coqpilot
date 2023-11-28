import {
    TextEditor,
    Uri,
} from "vscode";

import {
    BaseLanguageClient,
    RequestType,
    VersionedTextDocumentIdentifier,
    DocumentSymbolRequest,
    Disposable,
    DocumentSymbolParams,
    DocumentSymbol,
    Range,
    Position,
    DidOpenTextDocumentNotification,
    DidOpenTextDocumentParams,
    LogTraceNotification,
    ProtocolNotificationType,
    DidChangeTextDocumentParams,
    PublishDiagnosticsNotification,
    DidChangeTextDocumentNotification,
    SetTraceNotification,
    SetTraceParams,
    Diagnostic,
    TextDocumentIdentifier, 
    DidCloseTextDocumentNotification,
    DidCloseTextDocumentParams,
} from "vscode-languageclient";

import { 
    readFileSync, 
    openSync, 
    closeSync, 
    unlinkSync, 
    writeFileSync, 
    appendFileSync, 
} from "fs";

import { 
    GoalRequest, 
    GoalAnswer, 
    PpString, 
    hypToString, 
    FlecheDocument, 
    FlecheDocumentParams,
} from "../lib/types";

import { FileProgressManager } from "./progress";
import { VsCodeProgressBar } from "../extension/vscodeProgressBar";
import { getTextBeforePosition, toVPosition } from "./utils";
import { Theorem } from "../lib/pvTypes";
import { parseFleche } from "./flecheDocUtils";
import { StatusBarButton } from "../editor/enableButton";
import logger from "../extension/logger";
import { LLMIterator } from "../coqLlmInteraction/llmIterator";

export interface ProofViewInterface extends Disposable {
    /**
     * Calls coq-lsp at current cursor position to retrieve goals, 
     * formats them as an auxiliary theorem, and returns it.
     * IS RESPONSIBLE for opening the file located at `uri`. 
     * IS NOT RESPONSIBLE for deleting the file located at `uri`.
     * @param uri The uri of the aux document
     * @param text The text in which request is issued
     * @param position The position of the cursor
     * @returns The auxiliary theorem and the name of the theorem that hole is in
     */
    getAuxTheoremAtCurPosition(
        uri: Uri, 
        text: string,
        position: Position
    ): Promise<[string, string] | undefined>;

    /**
     * Takes an iterator over `{ ${proofWithoutProofAndQed} }` strings, for each proof,
     * inserts it into the end of the file, and check for errors.
     * IS NOT RESPONSIBLE for opening the file located at `uri`.
     * IS RESPONSIBLE for deleting the file located at `uri` after the call.
     * @param uri The uri of the aux document
     * @param proofs An iterator over proofs
     * @param thrStatement The statement of the theorem that is being proved
     * @returns An array of tuples, each tuple contains a proof, its typecheck result as boolean
     * and an error message, if any.
     * Invariant: the length of the returned array is <= the length of `theoremWithProofs`.
     * The array either contains all `false` or < `theoremWithProofs.length` `false` values 
     * and one `true` value.
     * 
     * Concurrency invariants: CheckTheorems is yet not assumed to be run from different 
     * threads simultaniously. However, as it is used in parallelized hole completion, it
     * becomes a synchronization point and requires mutexes, attached to this class. 
     * tl;dr: We use a mutex in this class to prevent data races when asynchroniously substituting holes. 
     */
    checkTheorems(
        uri: Uri, 
        proofs: LLMIterator, 
        thrStatement: string
    ): Promise<[string, boolean, string | null][]>;

    /**
     * Parses the file and returns a list of theorems.
     * @param editor The editor to parse
     * IS RESPONSIBLE for opening the file located at `uri`.
     * IS NOT RESPONSIBLE for deleting the file located at `uri`.
     */
    parseFile(editor: TextEditor): Promise<Theorem[]>;
    
    /**
     * Open the file at the given uri
     * @param uri The uri of the document to open (send request to coq-lsp)
     */
    openFile(uri: Uri): Promise<void>;

    /**
     * Close the file at the given uri
     * @param uri The uri of the document to close (send request to coq-lsp)
     */
    closeFile(uri: Uri): Promise<void>;
}

const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));

const goalReq = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
    "proof/goals"
);

const flecheDocReq = new RequestType<FlecheDocumentParams, FlecheDocument, void>(
    "coq/getDocument"
  );
  
export class ProofView implements ProofViewInterface {
    private client: BaseLanguageClient;
    private pendingProgress: boolean = false;
    private pendingDiagnostic: boolean = false;
    private awaitedDiagnostic: Diagnostic[] | null = null;
    private subscriptions: Disposable[] = [];
    private fileProgress: FileProgressManager;

    constructor(client: BaseLanguageClient, statusItem: StatusBarButton) {
        this.client = client;
        const progressBar = new VsCodeProgressBar(statusItem);
        this.fileProgress = new FileProgressManager(client, progressBar);
    }

    async getDocument(uri: Uri) {
        const params: DocumentSymbolParams = {
            textDocument: {
                uri: uri.toString()
            }
        };
        const response = await this.client.sendRequest(DocumentSymbolRequest.type, params);
        return response;
    }

    async getFlecheDocument(uri: Uri) {
        let textDocument = TextDocumentIdentifier.create(
            uri.toString(),
        );
        let params: FlecheDocumentParams = { textDocument };
        const doc = await this.client.sendRequest(flecheDocReq, params);
        
        return doc;
    };

    getTheoremClosestToPosition(
        position: Position, 
        document: DocumentSymbol[]
    ): [string, Position] | undefined {
        function isPositionAfterRangeStart(position: Position, range: Range): boolean {
            return range.start.line <= position.line && range.start.character <= position.character;
        };

        // Find closest theorem before the cursor
        let left = 0;
        let right = document.length - 1;
        let closestTheorem: DocumentSymbol | undefined = undefined;
        while (left <= right) {
            let mid = Math.floor((left + right) / 2);
            if (isPositionAfterRangeStart(position, document[mid].range)) {
                closestTheorem = document[mid];
                left = mid + 1;
            } else {
                right = mid - 1;
            }
        }

        if (!closestTheorem) {
            return undefined;
        }

        return [closestTheorem.name, closestTheorem.range.start];
    }

    async getAuxTheoremAtCurPosition(
        uri: Uri, 
        text: string,
        position: Position
    ): Promise<[string, string] | undefined> {
        const textBeforePos = getTextBeforePosition(text, toVPosition(position));
        await this.copyAndOpenFile(textBeforePos, uri);

        const goals = await this.client.sendRequest(goalReq, {
            textDocument: VersionedTextDocumentIdentifier.create(
                uri.toString(),
                1
            ),
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
        });
        
        const goal = goals?.goals?.goals?.shift() ?? undefined;
        if (!goal) {
            return undefined;
        }

        const auxTheoremConcl = goal?.ty;
        const theoremIndeces = goal?.hyps.map(hyp => `(${hypToString(hyp)})`).join(' ');
        const coqDoc = await this.getDocument(uri);
        const res = this.getTheoremClosestToPosition(position, coqDoc as DocumentSymbol[]); 
        if (!res) {
            return undefined;
        }

        const [thrName, _] = res;
        const auxTheoremStatement = `Lemma ${thrName}_aux_thr ${theoremIndeces} :\n   ${auxTheoremConcl}.`;

        return [auxTheoremStatement, thrName];
    }

    /**
     * Makes arbitrary document-change request to the coq-lsp client, then actively waits for
     * the coq-lsp to re-typecheck it. This function assumes that coq-lsp first sends 
     * "document fully" checked logtrace notification, and then sends final diagnostics.
     * TODO: "document fully checked" logtrace notification does not contain the uri of
     * the corresponding document, so, if there are multiple documents open there may occure 
     * a situation when when we accidently catch the other document's notification and 
     * after that start assuming its fully checked. 
     * For more garanties, I have added a check that the checked document is the same size
     * as the original one, but, anyways, this should be fixed in the future.
     * Maybe open a new-feature issue for coq-lsp
     * @param requestType Type of the request
     * @param params Params of the request 
     * @param uri Uri of the document we are changing 
     * @param lineNum Number of lines in this document
     * @param timeout Timeout in milliseconds
     * @returns An array of diagnostics, if any, otherwise []
     */
    async updateWithWait(
        requestType: ProtocolNotificationType<any, any>,
        params: any, 
        uri: Uri,
        lineNum: number,
        timeout: number = 50000,
        oldLineCount: number | null = null
    ): Promise<Diagnostic[]> {
        await this.client.sendNotification(requestType, params);

        this.pendingProgress = true;
        this.pendingDiagnostic = true;
        this.awaitedDiagnostic = null;

        this.fileProgress.subscribeForUpdates(uri.toString(), lineNum);
        this.subscriptions.push(this.client.onNotification(LogTraceNotification.type, (params) => {
            if (params.message.includes("document fully checked") && params.message.includes(`l: ${lineNum}`)) {
                this.pendingProgress = false;
            }
        })); 

        this.subscriptions.push(this.client.onNotification(PublishDiagnosticsNotification.type, (params) => {
            if (params.uri.toString() === uri.toString()) {
                this.pendingDiagnostic = false;
                this.awaitedDiagnostic = params.diagnostics;
                // I discovered that sometimes coq-lsp breaks when recieves an 
                // incorrectly nested proof, e.g. when inside curly braces we start adding 
                // multiple '-' characters to enumerate goals (whilst there is just one goal), 
                // coq-lsp breaks and stops serving fileProgress process. Such proofs are obviously incorrect
                // and we want to reject them. In such cases, coq-lsp sends a publishDiagnostics notification
                // with errors intil some Point, and then, if the proof continues and it is 
                // depply incorrect, something happens and coq-lsp breaks. As a workaround,
                // as we are interested only in the first error occured in the generated proof, 
                // we check if the last error is after the last line of the original document 
                // (before the TextDocumentChange request was issued). 
                if (oldLineCount && this.filterDiagnostics(params.diagnostics, { line: oldLineCount, character: 0 }) !== null) {
                    this.pendingProgress = false;
                }
            }
        }));

        while (timeout > 0 && (this.pendingProgress || this.pendingDiagnostic)) {
            await sleep(100);
            timeout -= 100;
        }

        if (
            timeout <= 0 ||
            this.pendingProgress || 
            this.pendingDiagnostic || 
            this.awaitedDiagnostic === null
        ) {
            throw new Error("Coq-lsp did not respond in time");
        }

        this.fileProgress.stopListening();

        return this.awaitedDiagnostic;
    }

    /**
     * Used to determine which diagnostics correspond to the theorem
     * we are interested in.
     * @param diagnostics An array of diagnostics
     * @param position The position to filter diagnostics by
     * @returns The first diagnostic's message that is after the given 
     * position or null if there is none
     */
    filterDiagnostics(diagnostics: Diagnostic[], position: Position): string | null {
        return diagnostics.filter(diag => diag.range.start.line >= position.line)
                          .filter(diag => diag.severity === 1) // 1 is error
                          .shift()?.message?.split('\n').shift() ?? null;
    }

    setTrace(level: "off" | "messages" | "verbose") {
        const params: SetTraceParams = {
            value: level
        };
        this.client.sendNotification(SetTraceNotification.type, params);
    }

    private async copyAndOpenFile(docText: string, newUri: Uri) {
        const lineCount = docText.split("\n").length - 1;

        // Open new file
        const fd = openSync(newUri.fsPath, "w");
        // Copy to it the contents of the old file
        writeFileSync(fd, docText);
        // Close the file
        closeSync(fd);
 
        // Request lsp to open the new file
        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: newUri.toString(),
                languageId: "coq",
                version: 1,
                text: docText
            }
        };

        await this.updateWithWait(DidOpenTextDocumentNotification.type, params, newUri, lineCount);
    }

    async openFile(uri: Uri) {
        const docText = readFileSync(uri.fsPath).toString();
        const lineCount = docText.split("\n").length - 1;

        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: uri.toString(),
                languageId: "coq",
                version: 1,
                text: docText
            }
        };

        await this.updateWithWait(DidOpenTextDocumentNotification.type, params, uri, lineCount);
    }

    async closeFile(uri: Uri) {
        const params: DidCloseTextDocumentParams = {
            textDocument: {
                uri: uri.toString(),
            }
        };

        await this.client.sendNotification(DidCloseTextDocumentNotification.type, params);
    }

    async parseFile(editor: TextEditor): Promise<Theorem[]> {
        const uri = editor.document.uri;
        const text = editor.document.getText();
        const lineNum = editor.document.lineCount - 1;
        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: uri.toString(),
                languageId: "coq",
                version: 1,
                text: text,
            }
        };

        await this.updateWithWait(DidOpenTextDocumentNotification.type, params, uri, lineNum);

        const doc = await this.getFlecheDocument(uri);
        const fd = parseFleche(doc, text.split("\n"));

        return fd;
    }

    private cleanProof(proof: string): string {
        // remove backticks because apparently everything crashes 
        // if gpt generates a proof embedded in 3 backticks
        // I didn't figure out why yet
        
        return proof.replace(/`/g, "");
    }

    async checkTheorems(
        uri: Uri, 
        proofs: LLMIterator, 
        thrStatement: string
    ): Promise<[string, boolean, string | null][]> {
        logger.info("Started type-checking proofs");

        let documentVersion = 1;

        // Open the file and read the context
        const context = readFileSync(uri.fsPath).toString();
        const lineNumContext = context.split("\n").length - 1;

        proofs.restart();
        const proofVerdicts: [string, boolean, string | null][] = [];

        while (true) {
            const result = await proofs.next(thrStatement);
            if (result.done) {
                break;
            }

            const proof = this.cleanProof(result.value);
            logger.info(proof);

            const prohibitedTactics = ["admit.", "Admitted.", "Abort."];
            if (prohibitedTactics.some(tactic => proof.includes(tactic))) {
                proofVerdicts.push([proof, false, "Proof contains 'Abort.' or 'Admitted.'"]);
                continue;
            }
            
            documentVersion += 1;

            // Append the proof to the end of the file
            appendFileSync(uri.fsPath, proof);

            // Notify the server about the change
            const versionedDoc = VersionedTextDocumentIdentifier.create(
                uri.toString(),
                documentVersion
            );

            const newText = context + proof;
            const params: DidChangeTextDocumentParams = {
                textDocument: versionedDoc,
                contentChanges: [{
                    text: newText
                }]
            };

            const newLineNum = newText.split("\n").length - 1;

            logger.info("Started typechecking proof: " + proof);
            const diags = await this.updateWithWait(
                DidChangeTextDocumentNotification.type, 
                params, uri, newLineNum, 50000, lineNumContext
            );
            logger.info("Finished typechecking proof");

            // Filter diagnostics by the line number of the context
            const errorMsg = this.filterDiagnostics(diags, { line: lineNumContext, character: 0 });

            // Remove the proof from the end of the file
            writeFileSync(uri.fsPath, context);

            if (errorMsg === null) {
                proofVerdicts.push([proof, true, null]);
                unlinkSync(uri.fsPath);
                return proofVerdicts;
            } else {
                proofVerdicts.push([proof, false, errorMsg]);
            }
        }

        // Delete aux file
        unlinkSync(uri.fsPath);

        return proofVerdicts;
    }

    dispose(): void {
        this.subscriptions.forEach((d) => d.dispose());
    }
}