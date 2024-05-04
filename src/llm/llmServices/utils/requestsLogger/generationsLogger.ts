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

/**
 * This class is responsible for logging the actual generations.
 * I.e. errors caused by the user or the extension are not the target ones.
 *
 * The main function of `GenerationLogger` is to keep the logs since the last success,
 * in order to provide them for the analysis of the time
 * needed to `LLMService` to become available again.
 *
 * Also, due to the `debug` mode, `GenerationLogger` can be used for debug purposes.
 */
export class GenerationsLogger {
    private readonly logsFile: SyncFile;
    private readonly recordsDelim = "@@@ ";

    /**
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

    logGenerationSucceeded(request: GenerationRequest, proofs: string[]) {
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

    logGenerationFailed(request: GenerationRequest, error: Error) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelName,
            "FAILURE",
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

    /**
     * This method returns logs since the last success exclusively!
     * In other words, the last success record (if it exists) is not included in the result.
     */
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

    /**
     * Clears the logs file or creates it if it doesn't exist.
     */
    resetLogs() {
        this.logsFile.createReset();
    }

    dispose() {
        this.logsFile.delete();
    }
}
