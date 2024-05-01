import { ChatHistory } from "../../chat";
import { ModelParams } from "../../modelParams";
import { nowTimestampMillis } from "../time";

import { DebugLoggerRecord, LoggerRecord } from "./loggerRecord";
import { SyncFile } from "./syncFile";

export interface GenerationRequest {
    params: ModelParams;
    choices: number;
}

export interface FromChatGenerationRequest extends GenerationRequest {
    chat: ChatHistory;
    estimatedTokens: number;
}

function isFromChatGenerationRequest(
    object: any
): object is FromChatGenerationRequest {
    return "chat" in object && "estimatedTokens" in object;
}

export class RequestsLogger {
    private readonly logsFile: SyncFile;
    private readonly recordsDelim = "@@@ ";

    /*
     * - When `debug` is false, logs only the necessary info:
     * timestamp, model name, response status and request info (choices and number of tokens sent).
     * Logs are being cleaned every time the last request succeeds.
     * - When `debug` is true, logs:
     * chat history, received completions and params of the model additionally.
     * Also, the logs are never cleaned automatically.
     */
    constructor(
        filePath: string,
        private readonly debug: boolean = false,
        cleanLogsOnStart: boolean = true
    ) {
        this.logsFile = new SyncFile(filePath);
        if (!this.logsFile.exists() || cleanLogsOnStart) {
            this.resetLogs();
        }
    }

    logRequestSucceeded(request: GenerationRequest, proofs: string[]) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelName,
            "SUCCESS",
            request.choices,
            isFromChatGenerationRequest(request)
                ? request.estimatedTokens
                : undefined
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
                isFromChatGenerationRequest(request) ? request.chat : undefined,
                request.params,
                proofs
            );
        }

        const newLog = `${this.recordsDelim}${record.serializeToString()}\n`;
        if (this.debug) {
            this.logsFile.append(newLog);
        } else {
            this.logsFile.write(newLog);
        }
    }

    logRequestFailed(request: GenerationRequest, error: Error) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelName,
            "FAILED",
            request.choices,
            isFromChatGenerationRequest(request)
                ? request.estimatedTokens
                : undefined,
            {
                typeName: error.name,
                message: error.message,
            }
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
                isFromChatGenerationRequest(request) ? request.chat : undefined,
                request.params
            );
        }

        const newLog = `${this.recordsDelim}${record.serializeToString()}\n`;
        this.logsFile.append(newLog);
    }

    readLogs(): LoggerRecord[] {
        const rawData = this.logsFile.read();
        const rawRecords = rawData.split(this.recordsDelim).slice(1);
        return rawRecords.map((rawRecord) =>
            this.debug
                ? DebugLoggerRecord.deserealizeFromString(rawRecord)[0]
                : LoggerRecord.deserealizeFromString(rawRecord)[0]
        );
    }

    // Note: EXCLUSIVE! I.e. last success record (if it exists) is not included in the result.
    readLogsSinceLastSuccess(): LoggerRecord[] {
        const records = this.readLogs();
        const invertedRow = [];
        for (let i = records.length - 1; i >= 0; i--) {
            if (records[i].responseStatus === "SUCCESS") {
                break;
            }
            invertedRow.push(records[i]);
        }
        return invertedRow.reverse();
    }

    resetLogs() {
        this.logsFile.createReset();
    }

    dispose() {
        this.logsFile.delete();
    }
}
