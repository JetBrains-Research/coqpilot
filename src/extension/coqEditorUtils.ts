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

    /**
     * Take a statement+proof as a string and return the proof 
     * without "Proof." and "Qed.".
     * This function assumes proof is correct and behaviour is undefined
     * in case when it is not.
     * @param thrProof The proof of a theorem.
     * @returns The proof without "Proof." and "Qed.".
     */
    extractProofString(proofString: string): string {
        const stringWithoutStatement = proofString.split('.').slice(1).join('.');
        const stringWithoutProof = stringWithoutStatement.replace(/Proof\./g, '');
        const tokensWithoutQed = stringWithoutProof.replace(/Qed\./g, '').split('.');

        return tokensWithoutQed.map((token) => token.trim()).join('. ');
    }
    
    async insertIntoRange(range: vscode.Range, text: string) {
        await this.editor.edit((editBuilder) => {
            editBuilder.replace(range, text);
        });
    }

    async insertAboveTheorem(theoremName: string, text: string) {
        let theoremRange = this.getTheoremRange(theoremName);
        if (theoremRange === undefined) {
            throw new Error("Theorem not found");
        }
        let theoremStart = theoremRange.start;
        let textToInsert = text + "\n\n";

        await this.editor.edit((editBuilder) => {
            editBuilder.insert(theoremStart, textToInsert);
        });
    }

    async insertIntoHole(theoremName: string, holeRangeLocal: vscode.Range, text: string) {
        let theoremRange = this.getTheoremRange(theoremName);
        if (theoremRange === undefined) {
            throw new Error("Theorem not found");
        }

        let holeRange = new vscode.Range(
            theoremRange.start.line + holeRangeLocal.start.line, holeRangeLocal.start.character,
            theoremRange.start.line + holeRangeLocal.start.line, holeRangeLocal.end.character
        );

        await this.insertIntoRange(holeRange, text);
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