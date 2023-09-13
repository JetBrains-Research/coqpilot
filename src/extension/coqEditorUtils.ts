import * as vscode from 'vscode';

export namespace CoqTokens {
    enum ThmToken {
        theorem = "Theorem",
        lemma = "Lemma",
        fact = "Fact",
        remark = "Remark",
        corollary = "Corollary",
        proposition = "Proposition",
        property = "Property"
    }

    enum ProofEndToken {
        qed = "Qed.",
        admitted = "Admitted.",
        abort = "Abort."
    }

    const thmTokenRegexp = "(?:" + Object.values(ThmToken).join("|") + ")";
    const proofEndTokenRegexp = "(?:" + Object.values(ProofEndToken).join("|") + ")";
    const theoremRegexp = new RegExp(`${thmTokenRegexp} [\\s\\S]*?${proofEndTokenRegexp}`, 'gm');

    export function getTheoremRegexp(theoremName: string): RegExp {
        return new RegExp(`${thmTokenRegexp} ${theoremName} [\\s\\S]*?${proofEndTokenRegexp}`, 'gm');
    }

    export function getTheoremRegexpNoName(): RegExp {
        return theoremRegexp;
    }
}

export class CoqEditorUtils {
    protected editor: vscode.TextEditor;

    constructor(editor: vscode.TextEditor | undefined) {
        if (editor === undefined) {
            throw new Error("Editor is undefined");
        }
        this.editor = editor;
    }

    getTheoremRange(theoremName: string): vscode.Range | undefined {
        let regexp = CoqTokens.getTheoremRegexp(theoremName);
        let text = this.editor.document.getText();
        let foundIndex = text.search(regexp);
        let match = text.match(regexp);

        if (match === null) {
            return undefined;
        } else if (match.length > 1) {
            throw new Error("More than one theorem with the same name found.");
        } 

        let foundMatchLength = match[0].length;        
        let theoremStart = this.editor.document.positionAt(foundIndex);
        let theoremEnd = this.editor.document.positionAt(foundIndex + foundMatchLength);

        return new vscode.Range(theoremStart, theoremEnd);
    }
    
    insertIntoRange(range: vscode.Range, text: string) {
        this.editor.edit((editBuilder) => {
            editBuilder.replace(range, text);
        });
    }

    getRangeOfSelection(): vscode.Range | undefined {
        let selection = this.editor.selection;
        if (selection.isEmpty) {
            return undefined;
        }
        return new vscode.Range(selection.start, selection.end);
    }

    findTheoremInSelection(): string | undefined {
        let range = this.getRangeOfSelection();
        if (range === undefined) {
            return undefined;
        }
        let text = this.editor.document.getText(range);

        const re = CoqTokens.getTheoremRegexpNoName();
        let theoremName = text.match(re);
        if (theoremName === null) {
            console.log("Theorem name not found");
            return undefined;
        }
        
        return theoremName[0].split(' ')[1];
    }
}