import {
    Position,
    TextEditor,
    Range
} from "vscode";

export async function insertCompletion(editor: TextEditor, proof: string, position: Position) {
    await editor.edit((editBuilder) => {
        editBuilder.insert(position, proof);
    });
}

export async function deleteTextFromRange(editor: TextEditor, range: Range) {
    await editor.edit((editBuilder) => {
        editBuilder.delete(range);
    });
}