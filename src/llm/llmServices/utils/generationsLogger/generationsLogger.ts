import {
    GenerationFailedError,
    LLMServiceError,
} from "../../../llmServiceErrors";
import {
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "../../llmService";
import { ModelParams } from "../../modelParams";
import { nowTimestampMillis } from "../time";

import { DebugLoggerRecord, LoggedError, LoggerRecord } from "./loggerRecord";
import { SyncFile } from "./syncFile";

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
    private static readonly recordsDelim = "@@@ ";
    static readonly censorString = "***censored***";

    /**
     * - When `debug` is false, logs only the necessary info:
     * timestamp, model name, response status and basic request info (choices and number of tokens sent).
     * Logs are being cleaned every time the last request succeeds.
     * - When `debug` is true, logs chat history, received completions and params of the model additionally.
     *   Also, the logs are never cleaned automatically.
     *
     * @param paramsPropertiesToCensor specifies properties of `ModelParams` (or its extension)
     * that will be replaced with the corresponding given values in logs. By default, it is `{apiKey: GenerationsLogger.censorString}`.
     */
    constructor(
        readonly filePath: string,
        private readonly debug: boolean = false,
        private readonly paramsPropertiesToCensor: Object = {
            apiKey: GenerationsLogger.censorString,
        },
        cleanLogsOnStart: boolean = true
    ) {
        this.logsFile = new SyncFile(this.filePath);
        if (!this.logsFile.exists() || cleanLogsOnStart) {
            this.resetLogs();
        }
    }

    logGenerationSucceeded(request: LLMServiceRequestSucceeded) {
        let record = new LoggerRecord(
            nowTimestampMillis(),
            request.params.modelId,
            "SUCCESS",
            request.choices,
            request.analyzedChat?.estimatedTokens
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
                request.analyzedChat?.chat,
                this.censorParamsProperties(request.params),
                request.generatedRawProofs
            );
        }

        const newLog = `${GenerationsLogger.recordsDelim}${record.serializeToString()}\n`;
        if (this.debug) {
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
            this.toLoggedError(
                this.extractAndValidateCause(request.llmServiceError)
            )
        );
        if (this.debug) {
            record = new DebugLoggerRecord(
                record,
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

    private extractAndValidateCause(llmServiceError: LLMServiceError): Error {
        if (!(llmServiceError instanceof GenerationFailedError)) {
            throw Error(
                `\`GenerationsLogger\` is capable of logging only generation errors, but got: "${this.toLoggedError(llmServiceError)}"`
            );
        }
        const cause = llmServiceError.cause;
        if (cause instanceof LLMServiceError) {
            throw Error(
                `received doubled-wrapped error to log, cause is instance of \`LLMServiceError\`: "${this.toLoggedError(llmServiceError)}"`
            );
        }
        return cause;
    }

    private censorParamsProperties<T extends ModelParams>(params: T): T {
        // no need in deep copies, but we shall not overwrite original params
        return {
            ...params,
            ...this.paramsPropertiesToCensor,
        };
    }

    private toLoggedError(error: Error): LoggedError {
        return {
            typeName: error.name,
            message: error.message,
        };
    }
}
