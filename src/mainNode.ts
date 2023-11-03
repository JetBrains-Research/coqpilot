import { ExtensionContext } from "vscode";
import { Coqpilot } from "./extension";

export let extension: Coqpilot | undefined;

export async function activate(context: ExtensionContext): Promise<void> {
    extension = await Coqpilot.init(context);
    context.subscriptions.push(extension);
}
  
export function deactivate() {
    extension.dispose();
}