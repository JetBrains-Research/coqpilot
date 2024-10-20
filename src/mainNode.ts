import { ExtensionContext } from "vscode";

import { CoqPilot } from "./extension/coqPilot";
import { StatusBarButton } from "./extension/statusBarButton";

export let extension: CoqPilot | undefined;
let statusBar: StatusBarButton | undefined = undefined;

export async function activate(context: ExtensionContext): Promise<void> {
    statusBar = new StatusBarButton(context, toggleExtension);
    statusBar.toggle();
}

async function startExtension(context: ExtensionContext) {
    if (!statusBar) {
        statusBar = new StatusBarButton(context, toggleExtension);
    }
    extension = await CoqPilot.create(context, statusBar);
    context.subscriptions.push(extension);
}

function stopExtension() {
    extension?.dispose();
    extension = undefined;
}

function toggleExtension(isActive: boolean, context: ExtensionContext) {
    if (isActive) {
        startExtension(context);
    } else {
        stopExtension();
    }
}

export function deactivate() {
    stopExtension();
    statusBar?.dispose();
}
