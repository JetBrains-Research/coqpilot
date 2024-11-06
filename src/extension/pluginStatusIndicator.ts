import {
    ExtensionContext,
    StatusBarAlignment,
    StatusBarItem,
    window,
} from "vscode";

import { pluginName } from "./coqPilot";

export class PluginStatusIndicator {
    private readonly statusBarItem: StatusBarItem;

    constructor(
        invocationCommand: string,
        private readonly context: ExtensionContext
    ) {
        this.statusBarItem = window.createStatusBarItem(
            StatusBarAlignment.Left,
            0
        );
        this.statusBarItem.show();

        this.context.subscriptions.push(this.statusBarItem);
        this.statusBarItem.command = invocationCommand;
    }

    updateStatusBar(isActive: boolean) {
        if (isActive) {
            this.statusBarItem.text = `$(debug-stop) ${pluginName}: Running`;
            this.statusBarItem.tooltip = "Click to stop the extension";
        } else {
            this.statusBarItem.text = `$(debug-start) ${pluginName}: Stopped`;
            this.statusBarItem.tooltip = "Click to start the extension";
        }
    }

    showInProgressSpinner() {
        this.statusBarItem.text = `$(sync~spin) ${pluginName}: In progress`;
        this.statusBarItem.tooltip = "Operation in progress...";
    }

    hideInProgressSpinner(isActive: boolean) {
        this.updateStatusBar(isActive);
    }

    dispose() {
        this.statusBarItem.dispose();
    }
}
