import { expect } from "earl";
import { TextDocument, Uri, window, workspace } from "vscode";

export async function checkDocumentContains(
    document: TextDocument,
    ...substrings: string[]
) {
    const originalContent = document.getText();
    expect(originalContent).toInclude(...substrings);
}

export class TextDocumentWrapper {
    private constructor(private readonly document: TextDocument) {}

    checkDocumentContains(...substrings: string[]) {
        return checkDocumentContains(this.document, ...substrings);
    }

    static async create(filePath: string): Promise<TextDocumentWrapper> {
        const doc = await workspace.openTextDocument(Uri.file(filePath));
        await window.showTextDocument(doc);
        return new TextDocumentWrapper(doc);
    }
}
