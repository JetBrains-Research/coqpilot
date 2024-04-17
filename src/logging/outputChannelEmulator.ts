import { appendFileSync, existsSync, writeFileSync } from "fs";
import { OutputChannel, ViewColumn } from "vscode";

export class OutputChannelEmulator implements OutputChannel {
    name: string;

    constructor(
        private logFilePath: string,
        name: string = "OutputChannelEmulator"
    ) {
        this.name = name;
        if (!existsSync(this.logFilePath)) {
            writeFileSync(this.logFilePath, "");
        }
    }

    append(value: string): void {
        appendFileSync(this.logFilePath, value);
    }

    appendLine(value: string): void {
        appendFileSync(this.logFilePath, value + "\n");
    }

    replace(value: string): void {
        writeFileSync(this.logFilePath, value);
    }

    clear(): void {
        writeFileSync(this.logFilePath, "");
    }

    show(preserveFocus?: boolean | undefined): void;

    show(
        column?: ViewColumn | undefined,
        preserveFocus?: boolean | undefined
    ): void;

    show(_column?: unknown, _preserveFocus?: unknown): void {
        throw new Error("Method not implemented.");
    }

    hide(): void {
        throw new Error("Method not implemented.");
    }

    dispose(): void {}
}
