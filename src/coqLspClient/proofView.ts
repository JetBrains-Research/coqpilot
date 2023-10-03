import {
    TextEditor,
    ExtensionContext,
    commands,
    Uri,
    Position as VSPos,
    Range as VSRange,
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
    TextDocumentContentChangeEvent,
    PublishDiagnosticsNotification,
    DidChangeTextDocumentNotification,
    SetTraceNotification,
    SetTraceParams,
    Diagnostic
} from "vscode-languageclient";

import { 
    readFileSync, 
    openSync, 
    closeSync, 
    existsSync,
    unlinkSync, 
    writeFileSync, 
    appendFileSync
} from "fs";

import { GoalRequest, GoalAnswer, PpString, hypToString } from "../lib/types";

interface ProofViewInterface {
    /**
     * Calls coq-lsp at current cursor position to retrieve goals, 
     * formats them as an auxiliary theorem, and returns it.
     * @param editor The editor to retrieve goals from
     * @returns The auxiliary theorem and its start position
     */
    getAuxTheoremAtCurPosition(editor: TextEditor): Promise<[string, Position] | undefined>;

    /**
     * Takes an array of `${theorem}${proof}` strings, for each theorem,
     * inserts it into given position, and check for errors.
     * @param uri The uri of the document
     * @param precedingContext The context 
     * @param theoremsWithProofs The array of `${theorem}${proof}` strings
     * @returns An array of tuples, each tuple contains a boolean and an error message, if any.
     * Invariant: the length of the returned array is <= the length of `theoremWithProofs`.
     * The array either contains all `false` or < `theoremWithProofs.length` `false` values 
     * and one `true` value.
     */
    checkTheorems(
        uri: Uri, 
        precedingContext: string,
        theoremsWithProofs: string[]
    ): Promise<[boolean, string | null][]>;
}

const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));

const goalReq = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
    "proof/goals"
);
  
export class ProofView implements ProofViewInterface, Disposable {
    private client: BaseLanguageClient;
    private pendingProgress: boolean;
    private pendingDiagnostic: boolean;
    private awaitedDiagnostic: Diagnostic[] | null;

    constructor(client: BaseLanguageClient, context: ExtensionContext) {
        this.client = client;

        function solverCommand(command: string, fn: (editor: TextEditor) => void) {
            let disposable = commands.registerTextEditorCommand(
                "coqpilot." + command,
                fn
            );
            context.subscriptions.push(disposable);
        }

        solverCommand("get_document", this.runGeneration.bind(this));
    }

    async getDocument(editor: TextEditor) {
        let uri = editor.document.uri;
        const params: DocumentSymbolParams = {
            textDocument: {
                uri: uri.toString()
            }
        };
        const response = await this.client.sendRequest(DocumentSymbolRequest.type, params);
        return response;
    }

    getTheoremClosestToPosition(position: Position, document: DocumentSymbol[]): [string, Position] | undefined {
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

    async getAuxTheoremAtCurPosition(editor: TextEditor): Promise<[string, Position] | undefined> {
        let uri = editor.document.uri;
        let version = editor.document.version;
        let position = editor.selection.active;

        const goals = await this.client.sendRequest(goalReq, {
            textDocument: VersionedTextDocumentIdentifier.create(
                uri.toString(),
                version
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
        const coqDoc = await this.getDocument(editor);
        const res = this.getTheoremClosestToPosition(position, coqDoc as DocumentSymbol[]); 
        if (!res) {
            return undefined;
        }

        const [thrName, thrPos] = res;
        const auxTheoremStatement = `Lemma aux_thr_${thrName} ${theoremIndeces} :\n   ${auxTheoremConcl}.`;

        return [auxTheoremStatement, thrPos];
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
    ): Promise<Diagnostic[]> {
        await this.client.sendNotification(requestType, params);

        this.pendingProgress = true;
        this.pendingDiagnostic = true;
        this.awaitedDiagnostic = null;

        this.client.onNotification(LogTraceNotification.type, (params) => {
            if (params.message.includes("document fully checked") && params.message.includes(`l: ${lineNum}`)) {
                this.pendingProgress = false;
            } else {
                console.log(params.message, lineNum);
            }
        }); 

        this.client.onNotification(PublishDiagnosticsNotification.type, (params) => {
            if (params.uri.toString() === uri.toString()) {
                this.pendingDiagnostic = false;
                this.awaitedDiagnostic = params.diagnostics;
            }
        });

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
        return diagnostics.filter(diag => diag.range.start.line > position.line)
                          .filter(diag => diag.severity === 1) // 1 is error
                          .shift()?.message?.split('\n').shift() ?? null;
    }

    private setTrace(level: "off" | "messages" | "verbose") {
        const params: SetTraceParams = {
            value: level
        };
        this.client.sendNotification(SetTraceNotification.type, params);
    }

    private makeAuxfname(uri: Uri): Uri {
        let auxFilePath = uri.fsPath.replace(/\.v$/, "_aux.v");
        if (existsSync(auxFilePath)) {
            const randomSuffix = Math.floor(Math.random() * 1000000);
            auxFilePath = auxFilePath.replace(/\.v$/, `_${randomSuffix}.v`);
        }
        
        return Uri.file(auxFilePath);
    }

    private async openCurDocument(editor: TextEditor) {
        this.setTrace("verbose");

        const uri = editor.document.uri;
        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: uri.toString(),
                languageId: "coq",
                version: 1,
                text: editor.document.getText()
            }
        };

        await this.updateWithWait(DidOpenTextDocumentNotification.type, params, uri, editor.document.lineCount - 1);
    }

    async runGeneration(editor: TextEditor) {
        // const auxFile = this.makeAuxfname(editor.document.uri);
        await this.openCurDocument(editor);

        const res = await this.getAuxTheoremAtCurPosition(editor);
        // console.log()
        if (!res) {
            console.log("No goal at cursor");
            return;
        }
        const [thr, pos] = res;
        const proofs = [
            thr + "\nProof. simpl. Qed.",
            // thr + "\nProof. reflexivity. Qed.",
            // thr + "\nProof. kek. Qed.",
            // thr + "\nProof. auto. Qed.",
        ];

        const uri = editor.document.uri;
        const endPos = new VSPos(pos.line, pos.character);
        const precedingContext = editor.document.getText(new VSRange(new VSPos(0, 0), endPos));

        const verdicts = await this.checkTheorems(uri, precedingContext, proofs);

        console.log("VERDICTS", verdicts);
    }

    async checkTheorems(
        uri: Uri, 
        precedingContext: string, 
        theoremsWithProofs: string[]
    ): Promise<[boolean, string | null][]> {
        const context = precedingContext + "\n\n";
        const lineNumContext = context.split("\n").length - 1;

        const auxUri = this.makeAuxfname(uri);

        const fd = openSync(auxUri.fsPath, "w");
        writeFileSync(fd, context);

        // Notify coq-lsp about the new aux file
        const params: DidOpenTextDocumentParams = {
            textDocument: {
                uri: auxUri.toString(),
                languageId: "coq",
                version: 1,
                text: context
            }
        };

        await this.updateWithWait(DidOpenTextDocumentNotification.type, params, auxUri, lineNumContext);
        let documentVersion = 1;
        const proofVerdicts: [boolean, string | null][] = [];

        for(const proof of theoremsWithProofs) {
            documentVersion += 1;
            appendFileSync(fd, proof);
            const versionedDoc = VersionedTextDocumentIdentifier.create(
                auxUri.toString(),
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
            const diags = await this.updateWithWait(DidChangeTextDocumentNotification.type, params, auxUri, newLineNum);
            const errorMsg = this.filterDiagnostics(diags, { line: lineNumContext, character: 0 });

            // unlinkSync(auxFilePath); 

            proofVerdicts.push([errorMsg === null, errorMsg]);
        }

        return proofVerdicts;
    }

    dispose(): void {
        this.client.dispose();
    }

}