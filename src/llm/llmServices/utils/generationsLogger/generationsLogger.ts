import { buildErrorCompleteLog } from "../../../../utils/errorsUtils";
import { illegalState } from "../../../../utils/throwErrors";
import { nowTimestampMillis } from "../../../../utils/time";
import {
    GenerationFailedError,
    LLMServiceError,
} from "../../../llmServiceErrors";
import {
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "../../commonStructures/llmServiceRequest";
import { ModelParams } from "../../modelParams";

import { DebugLoggerRecord, LoggedError, LoggerRecord } from "./loggerRecord";
import { SyncFile } from "./syncFile";

export interface GenerationsLoggerSettings {
    debug: boolean;
    paramsPropertiesToCensor: Object;
    cleanLogsOnStart: boolean;
}

/**
 * This class is responsible for logging the actual generations.
 * I.e. errors caused by the user or the extension are not the target ones.
 *
 * The core functionality of `GenerationLogger` is to keep the logs since the last success,
 * in order to provide them for the analysis of the time
 * needed to `LLMService` to become available again.
 *
 * Also, due to the `debug` mode, `GenerationLogger` can be used for debug purposes.
 *
 * *Implementation note:* the `GenerationsLogger` currently writes logs to a file as plain text,
 * which could theoretically result in performance overhead. However, in production mode,
 * logs are cleaned after each successful generation, keeping the file size small most of the time.
 * Thus, the overhead from handling larger files is negligible.
 * Although some costs of working with plain text may remain, tests have not shown any performance
 * degradation in practice. If performance issues arise in the future, consider modifying the
 * string serialization/deserialization within `SyncFile`.
 */
export class GenerationsLogger {
    private readonly logsFile: SyncFile;
    private static readonly recordsDelim = "@@@ ";

    static readonly censorString = "***censored***";

    /**
     * About settings.
     *
     * - When `debug` is false, logs only the necessary info:
     * timestamp, model name, response status and basic request info (choices and number of tokens used).
     * Logs are being cleaned every time the last request succeeds.
     * - When `debug` is true, logs context theorems, chat history, received completions,
     *   and params of the model additionally. Also, the logs are never cleaned automatically.
     *
     * `paramsPropertiesToCensor` specifies properties of `ModelParams` (or its extension)
     * that will be replaced with the corresponding given values in logs.
     * An example `paramsPropertiesToCensor`: `{apiKey: GenerationsLogger.censorString}`.
     * To disable censorship, pass an empty object: `{}`.
     */
    constructor(
        readonly filePath: string,
        private readonly settings: GenerationsLoggerSettings
    ) {
        this.logsFile = new SyncFile(this.filePath);
        if (!this.logsFile.exists() || this.settings.cleanLogsOnStart) {
            this.resetLogs();
        }
    }

    logGenerationSucceeded(request: LLMServiceRequestSucceeded) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelId,
            "SUCCESS",
            request.choices,
            request.analyzedChat?.estimatedTokens,
            request.tokensSpentInTotal
        );
        if (this.settings.debug) {
            record = new DebugLoggerRecord(
                record,
                request.analyzedChat?.contextTheorems,
                request.analyzedChat?.chat,
                this.censorParamsProperties(request.params),
                request.generatedRawProofs.map(
                    (contentItem) => contentItem.content
                ) // TODO: maybe support per-item generation tokens
            );
        }

        const newLog = `${GenerationsLogger.recordsDelim}${record.serializeToString()}\n`;
        if (this.settings.debug) {
            this.logsFile.append(newLog);
        } else {
            this.logsFile.write(newLog);
        }
    }

    logGenerationFailed(request: LLMServiceRequestFailed) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelId,
            "FAILURE",
            request.choices,
            request.analyzedChat?.estimatedTokens,
            undefined,
            this.toLoggedError(
                this.extractAndValidateCause(request.llmServiceError)
            )
        );
        if (this.settings.debug) {
            record = new DebugLoggerRecord(
                record,
                request.analyzedChat?.contextTheorems,
                request.analyzedChat?.chat,
                this.censorParamsProperties(request.params)
            );
        }

        const newLog = `${GenerationsLogger.recordsDelim}${record.serializeToString()}\n`;
        this.logsFile.append(newLog);
    }

    readLogs(): LoggerRecord[] {
        const rawData = this.logsFile.read();
        const rawRecords = rawData
            .split(GenerationsLogger.recordsDelim)
            .slice(1);
        return rawRecords.map((rawRecord) =>
            this.settings.debug
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

    private extractAndValidateCause(llmServiceError: LLMServiceError): Error {
        if (!(llmServiceError instanceof GenerationFailedError)) {
            illegalState(
                "`GenerationsLogger` is capable of logging only generation errors, ",
                `but got: ${buildErrorCompleteLog(llmServiceError)}`
            );
        }
        const cause = llmServiceError.cause;
        if (cause instanceof LLMServiceError) {
            illegalState(
                "received doubled-wrapped error to log, ",
                "cause is instance of `LLMServiceError`: ",
                buildErrorCompleteLog(cause)
            );
        }
        return cause;
    }

    private censorParamsProperties<T extends ModelParams>(params: T): T {
        // no need in deep copies, but we shall not overwrite original params
        return {
            ...params,
            ...this.settings.paramsPropertiesToCensor,
        };
    }

    private toLoggedError(error: Error): LoggedError {
        return {
            typeName: error.name,
            message: error.message,
        };
    }
}
