import { Position, Range, TextEditor, window } from "vscode";

export async function insertCompletion(
    editor: TextEditor,
    proof: string,
    position: Position
) {
    await editor.edit((editBuilder) => {
        editBuilder.insert(position, proof);
    });
}

export async function deleteTextFromRange(editor: TextEditor, range: Range) {
    await editor.edit((editBuilder) => {
        editBuilder.delete(range);
    });
}

export function highlightTextInEditor(range: Range) {
    const editorDecorationType = window.createTextEditorDecorationType({
        backgroundColor: `rgba(0,255,0,0.5)`,
    });
    setTimeout(
        () => window.activeTextEditor?.setDecorations(editorDecorationType, []),
        2000
    );
    window.activeTextEditor?.setDecorations(editorDecorationType, [range]);
}
