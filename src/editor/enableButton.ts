import { 
    StatusBarItem,
    ThemeColor,
    window, 
    StatusBarAlignment, 
    Disposable
} from "vscode";

/* eslint-disable @typescript-eslint/naming-convention */
export enum StatusBarState {
    Activating,
    Running,
    Failed,
    Stopped
}
/* eslint-enable @typescript-eslint/naming-convention */

export class StatusBarButton implements Disposable {
    private item: StatusBarItem;
    private status: StatusBarState;

    get runStatus(): StatusBarState {
        return this.status;
    }

    constructor() {
        this.item = window.createStatusBarItem(
            "coqpilot.enable",
            StatusBarAlignment.Left,
            0
        );
        this.item.command = "coqpilot.toggle";
        this.item.text = "coqpilot (activating)";
        this.status = StatusBarState.Activating;
        this.item.show();
    }

    updateClientStatus(isClientRunning: boolean) {
        if (isClientRunning) {
            this.item.text = "$(check) coqpilot";
            this.item.backgroundColor = undefined;
            this.item.tooltip = "coqpilot is running. Click to disable.";
            this.status = StatusBarState.Running;
        } else {
            this.item.text = "$(circle-slash) coqpilot (stopped)";
            this.item.backgroundColor = new ThemeColor(
                "statusBarItem.warningBackground"
            );
            this.item.tooltip = "coqpilot has been disabled. Click to enable.";
            this.status = StatusBarState.Stopped;
        }
    }

    updateText(text: string) {
        this.item.text = text;
    }

    finishProgress() {
        this.updateClientStatus(true);
    }

    setFailedStatus(emsg: string) {
        this.item.text = "$(circle-slash) coqpilot (failed to start)";
        this.item.backgroundColor = new ThemeColor(
            "statusBarItem.errorBackground"
        );
        this.item.tooltip = `coqpilot couldn't start: ${emsg} Click to retry.`;
        this.status = StatusBarState.Failed;
    }

    dispose() {
        this.item.dispose();
    }
}