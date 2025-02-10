import { appendFileSync, writeFileSync } from "fs";
import { OutputChannel, ViewColumn } from "vscode";

import { unsupported } from "../utils/throwErrors";

export class OutputChannelEmulator implements OutputChannel {
    name: string;

    constructor(
        private logFilePath: string,
        name: string = "OutputChannelEmulator"
    ) {
        this.name = name;
        writeFileSync(this.logFilePath, "");
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
        unsupported("method not implemented");
    }

    hide(): void {
        unsupported("method not implemented");
    }

    dispose(): void {}
}
