import {
    ExtensionContext,
    StatusBarAlignment,
    StatusBarItem,
    commands,
    window,
} from "vscode";

import { pluginId, pluginName } from "./coqPilot";

// TODO: [LspCoreRefactor] Looks a bit dirty, refactor
export class StatusBarButton {
    private statusBarItem: StatusBarItem;
    private isActive: boolean;
    private context: ExtensionContext;
    private toggleCallback: (
        isActive: boolean,
        context: ExtensionContext
    ) => void;

    constructor(
        context: ExtensionContext,
        toggleCallback: (isActive: boolean, context: ExtensionContext) => void
    ) {
        this.context = context;
        this.isActive = false;
        this.toggleCallback = toggleCallback;

        this.statusBarItem = window.createStatusBarItem(
            StatusBarAlignment.Left,
            0
        );
        this.updateStatusBar();

        this.statusBarItem.show();
        this.context.subscriptions.push(this.statusBarItem);

        const command = `${pluginId}.toggleExtension`;
        this.statusBarItem.command = command;
        const toggleCommand = commands.registerCommand(
            command,
            this.toggle.bind(this)
        );
        this.context.subscriptions.push(toggleCommand);
    }

    toggle() {
        this.isActive = !this.isActive;
        this.updateStatusBar();
        this.toggleCallback(this.isActive, this.context);
    }

    private updateStatusBar() {
        if (this.isActive) {
            this.statusBarItem.text = `$(debug-stop) ${pluginName}: Running`;
            this.statusBarItem.tooltip = "Click to stop the extension";
        } else {
            this.statusBarItem.text = `$(debug-stop) ${pluginName}: Stopped`;
            this.statusBarItem.tooltip = "Click to start the extension";
        }
    }

    public showSpinner() {
        this.statusBarItem.text = `$(sync~spin) ${pluginName}: In progress`;
        this.statusBarItem.tooltip = "Operation in progress...";
    }

    public hideSpinner() {
        this.updateStatusBar();
    }

    public dispose() {
        this.statusBarItem.dispose();
    }
}
