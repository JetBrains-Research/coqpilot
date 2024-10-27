import { ExtensionContext } from "vscode";

import { CoqPilot } from "./extension/coqPilot";

export let extension: CoqPilot | undefined;

export async function activate(context: ExtensionContext): Promise<void> {
    extension = await CoqPilot.create(context);
    context.subscriptions.push(extension);
}

export function deactivate() {
    extension?.dispose();
}
