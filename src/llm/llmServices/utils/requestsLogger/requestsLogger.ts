import * as fs from "fs";
import * as path from "path";

import { ChatHistory } from "../../chat";
import { ModelParams } from "../../modelParams";

import { DebugLoggerRecord, LoggerRecord } from "./loggerRecord";

export interface GenerateFromChatRequest {
    chat: ChatHistory;
    estimatedTokens: number;
    params: ModelParams;
    choices: number;
}

export class RequestsLogger {
    /*
     * - When `debug` is false, logs only the necessary info:
     * timestamp, model name, response status and request info (choices and number of tokens sent).
     * Logs are being cleaned every time the last request succeeds.
     * - When `debug` is true, logs:
     * chat history, received completions and params of the model additionally.
     * Also, the logs are never cleaned automatically.
     */
    constructor(
        private readonly filePath: string,
        private readonly debug: boolean = false,
        cleanLogsOnStart: boolean = true
    ) {
        console.log(cleanLogsOnStart);
        if (!fs.existsSync(filePath) || cleanLogsOnStart) {
            this.resetLogs();
        }
    }

    private readonly encoding = "utf-8";
    private readonly recordsDelim = "@@@ ";

    logRequestSucceeded(request: GenerateFromChatRequest, proofs: string[]) {
        let record = new LoggerRecord(
            this.getNowTimestamp(),
            request.params.modelName,
            "SUCCESS",
            request.choices,
            request.estimatedTokens
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
                request.chat,
                request.params,
                proofs
            );
        }

        const newLog = `${this.recordsDelim}${record.serializeToString()}\n`;
        if (this.debug) {
            fs.appendFileSync(this.filePath, newLog, this.encoding);
        } else {
            fs.writeFileSync(this.filePath, newLog, this.encoding);
        }
    }

    logRequestFailed(request: GenerateFromChatRequest, error: Error) {
        let record = new LoggerRecord(
            this.getNowTimestamp(),
            request.params.modelName,
            "FAILED",
            request.choices,
            request.estimatedTokens,
            {
                typeName: error.name,
                message: error.message,
            }
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
                request.chat,
                request.params
            );
        }

        const newLog = `${this.recordsDelim}${record.serializeToString()}\n`;
        fs.appendFileSync(this.filePath, newLog, this.encoding);
    }

    readLogs(): LoggerRecord[] {
        const rawData = fs.readFileSync(this.filePath, this.encoding);
        const rawRecords = rawData.split(this.recordsDelim).slice(1);
        return rawRecords.map((rawRecord) =>
            this.debug
                ? DebugLoggerRecord.deserealizeFromString(rawRecord)[0]
                : LoggerRecord.deserealizeFromString(rawRecord)[0]
        );
    }

    resetLogs() {
        fs.mkdirSync(path.dirname(this.filePath), { recursive: true });
        fs.writeFileSync(this.filePath, "");
    }

    dispose() {
        fs.unlinkSync(this.filePath);
    }

    private getNowTimestamp(): Date {
        return new Date();
    }
}
