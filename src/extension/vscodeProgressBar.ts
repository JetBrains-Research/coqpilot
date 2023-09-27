import { ProgressBar } from "coqlsp-client";
import * as vscode from 'vscode';

export class VsCodeProgressBar extends ProgressBar {
    private progressBar: vscode.StatusBarItem | undefined;
    private percentage: number = 0;
    private totalLoc: number | undefined = undefined;

    constructor() {
        super(
            (newCount: number) => {
                let total = this.totalLoc;
                if (total === undefined || this.progressBar === undefined) {
                    throw new Error("Progress bar is not initialized");
                }
                this.percentage = newCount / total * 100;

                this.progressBar.text = `Coqpilot progress: ${this.percentage.toFixed(0)}%`;
            },
            (total: number) => {
                this.totalLoc = total;
                this.progressBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
                this.progressBar.text = 'Progress: 0%';
                this.progressBar.show();
            },
            () => {
                if (this.progressBar !== undefined) {
                    this.progressBar.dispose();
                }
            }
        );
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