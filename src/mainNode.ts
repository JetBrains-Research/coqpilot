import { ExtensionContext } from "vscode";
import { Coqpilot } from "./extension";

let extension: Coqpilot | undefined;

export async function activate(context: ExtensionContext): Promise<void> {
    extension = await Coqpilot.init(context);
    context.subscriptions.push(extension);
}
  
export function deactivate() {
    extension.dispose();
}