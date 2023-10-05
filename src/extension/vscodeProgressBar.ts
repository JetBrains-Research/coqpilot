import { ProgressBar } from "./progressBar";
import * as vscode from 'vscode';
import { StatusBarButton } from "../editor/enableButton";

export class VsCodeProgressBar extends ProgressBar {
    private statusItem: StatusBarButton;
    private percentage: number = 0;
    private totalLoc: number | undefined = undefined;

    constructor(statusItem: StatusBarButton) {
        super(
            (newCount: number) => {
                let total = this.totalLoc;
                if (total === undefined) {
                    throw new Error("Progress bar is not initialized");
                }
                this.percentage = newCount / total * 100;

                this.statusItem.updateText(`Coqpilot progress: ${this.percentage.toFixed(0)}%`);
            },
            (total: number) => {
                this.totalLoc = total;
                this.statusItem.updateText('Coqpilot progress: 0%');
            },
            () => {
                this.statusItem.finishProgress();
            }
        );

        this.statusItem = statusItem;
    }
}

const sleep = (time: number) => {
    return new Promise((resolve) => {
        setTimeout(() => {
            resolve(true);
        }, time);
    });
};

export class VsCodeSpinningWheelProgressBar extends ProgressBar {
    customCancellationToken: vscode.CancellationTokenSource | null = null;
    timeout: number = 300; // seconds

    constructor() {
        super(
            (_: number) => {},
            (_: number) => {
                vscode.window.withProgress({
                    location: vscode.ProgressLocation.Window,
                    cancellable: true,
                    title: 'Fetching LLM'
                }, async (_progress, _token) => {
                    return new Promise((async (resolve) => {
                        this.customCancellationToken = new vscode.CancellationTokenSource();
                
                        this.customCancellationToken.token.onCancellationRequested(() => {
                        this.customCancellationToken?.dispose();
                        this.customCancellationToken = null;
                
                        resolve(null);
                        return;
                    });
                    for (let i = 0; i < this.timeout; i++) {
                        await sleep(1000);
                    }        
                    resolve(null);
                    }));
                });
            },
            () => {
                if (this.customCancellationToken) {
                    this.customCancellationToken.cancel();
                }
            }
        );
    }
}