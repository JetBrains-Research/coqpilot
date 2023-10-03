import {
    Position,
    Uri,
    WorkspaceEdit,
    workspace,
} from "vscode";

import {
    BaseLanguageClient,
    NotificationType,
    RequestType,
    VersionedTextDocumentIdentifier,
    PublishDiagnosticsParams,
    WorkDoneProgress
} from "vscode-languageclient";

import { GoalRequest, GoalAnswer, PpString, hypToString } from "../lib/types";
  
const infoReq = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
    "proof/goals"
);

const coqFileDiags = new NotificationType<PublishDiagnosticsParams>(
    "textDocument/publishDiagnostics"
);

async function edit(f: (e: WorkspaceEdit) => void): Promise<void> {
    const e = new WorkspaceEdit();
    f(e);
    await workspace.applyEdit(e);
}
  
export class GoalsManager {
    isWaitingForDiagnostic: boolean;
    potentialProof: string | undefined;

    constructor() {
        this.isWaitingForDiagnostic = false;
        this.potentialProof = undefined;
    }
  
    // notify the display that we are waiting for info
    requestSent(_: GoalRequest) {
        console.log("requestSent");
    }
  
    // notify the info panel that we have fresh goals to render
    requestDisplay(goals: GoalAnswer<PpString>) {
        console.log("GOAAALS", goals);
    }
  
    // notify the info panel that we found an error
    requestError(e: any) {
        console.log("requestError", e);
    }
  
    // LSP Protocol extension for Goals
    sendGoalsRequest(client: BaseLanguageClient, params: GoalRequest) {
        this.requestSent(params);
        client.sendRequest(infoReq, params).then(
            (goals) => this.requestDisplay(goals),
            (reason) => this.requestError(reason)
        );
    }

    async checkAuxLemma(
        client: BaseLanguageClient,
        uri: Uri,
        version: number,
        position: Position
    ) {
        let textDocument = VersionedTextDocumentIdentifier.create(
            uri.toString(),
            version
        );
        
        let strCursor: GoalRequest = {
            textDocument,
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
        };

        client.sendRequest(infoReq, strCursor).then(
            async (goals) => {
                const goal = goals?.goals?.goals?.shift();
                const auxTheoremConcl = goal?.ty;
                console.log(goal?.hyps);
                const auxTheoremStatement = `Lemma aux_lemma_temp ${goal?.hyps.map(hyp => `(${hypToString(hyp)})`).join(' ')} :\n   ${auxTheoremConcl}.`;
                const proof = `Proof. auto. Qed.`;
                const auxTheorem = `${auxTheoremStatement}\n${proof}\n`;

                const newPos = new Position(position.line + 2, 0);

                this.isWaitingForDiagnostic = true;
                this.potentialProof = auxTheorem;
                await edit(e => {
                    e.insert(uri, newPos, auxTheorem);
                });

                client.onNotification(coqFileDiags, (params) => {
                    if (params.uri.toString() !== uri.toString()) {
                        return;
                    } 
                    if (this.isWaitingForDiagnostic) {
                        this.isWaitingForDiagnostic = false;
                        console.log("DIAGS", params.diagnostics.map(d => d.message));
                    }
                }); 

                // client.onNotification

                console.log("DIAGS", client.diagnostics.get(uri).map(d => d.message));

                console.log(auxTheoremStatement);
            
                // 3. upload original document to "restore" it
                // await edit(e => {
                //     const r = new Range(commandPosition, commandPosition.translate(0, 1 + command.length));
                //     e.delete(documentUri, r);
                // });
            
                // 4. process messages and return results (temp)
                // if (response.error) {
                //     throw new Error(convertToString(response.error));
                // }
                // else {
                //     return response;
                // }
            },
            (reason) => this.requestError(reason)
        );
    }
  
    updateFromServer(
        client: BaseLanguageClient,
        uri: Uri,
        version: number,
        position: Position
    ) {
        let textDocument = VersionedTextDocumentIdentifier.create(
            uri.toString(),
            version
        );
        
        let strCursor: GoalRequest = {
            textDocument,
            position,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            pp_format: "Str",
        };

        this.sendGoalsRequest(client, strCursor);
    }

    dispose() {}
}