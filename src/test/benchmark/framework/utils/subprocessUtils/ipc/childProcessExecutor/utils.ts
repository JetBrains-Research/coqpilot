import { ValidateFunction } from "ajv";
import * as child from "child_process";

import { failedAjvValidatorErrorsAsString } from "../../../../../../../utils/ajvErrorsHandling";
import { stringifyAnyValue } from "../../../../../../../utils/printers";
import { BenchmarkingLogger } from "../../../../logging/benchmarkingLogger";
import { PromiseExecutor } from "../../../promiseUtils";
import { IPCError } from "../ipcError";
import { IPCMessage, createStopIPCMessage } from "../ipcProtocol";

import { ExecutionResult } from "./executionResult";

export namespace ChildProcessExecutorUtils {
    export interface LifetimeObjects<ResultType, T> {
        subprocess: child.ChildProcess | undefined;
        executionLogger: BenchmarkingLogger;
        enableProcessLifetimeDebugLogs: boolean;
        promiseExecutor: PromiseExecutor<ExecutionResult<T>>;
        resultMapper: (result: ResultType) => T;
        debug: ConditionalExecutionLoggerDebug;
    }

    export type ConditionalExecutionLoggerDebug = (message: string) => void;

    export function buildDebugExecutionLoggerShortcut(
        executionLogger: BenchmarkingLogger,
        enableProcessLifetimeDebugLogs: boolean
    ): ConditionalExecutionLoggerDebug {
        return (message: string) => {
            if (enableProcessLifetimeDebugLogs) {
                executionLogger.debug(message);
            }
        };
    }

    export function rejectOnIPCError<ResultType, T>(
        errorMessage: string,
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        const asOneRecord = lifetime.executionLogger.asOneRecord();
        asOneRecord.error(
            "Process execution failed due to inter-process-communication error"
        );
        if (lifetime.enableProcessLifetimeDebugLogs) {
            asOneRecord.debug(`Cause: ${errorMessage}`);
        }
        finishSubprocess(lifetime);
        lifetime.promiseExecutor.reject(new IPCError(errorMessage));
    }

    export function rejectOnInvalidIPCMessageSchemaError<
        IPCMessageType extends IPCMessage,
        ResultType,
        T,
    >(
        ipcMessageTypeName: string,
        ipcMessage: IPCMessageType,
        failedValidator: ValidateFunction<IPCMessageType>,
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        rejectOnIPCError(
            [
                `received IPC ${ipcMessageTypeName}${ipcMessageTypeName === "" ? "" : " "}message `,
                `of invalid structure ${stringifyAnyValue(ipcMessage)}: `,
                `${failedAjvValidatorErrorsAsString(failedValidator)}`,
            ].join(""),
            lifetime
        );
    }

    export function finishSubprocess<ResultType, T>(
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        const subprocess = lifetime.subprocess;
        if (subprocess === undefined) {
            return;
        }
        if (subprocess.exitCode === null) {
            /*
             * Subprocess is still running, it's needed to be stopped.
             * Note: we don't try to send a signal to the subprocess,
             * because it doesn't give any guarantees on subprocess termination and
             * it may cause undefined behaviour (if the subprocess already exited and
             * another process with the same PID receives this signal).
             */
            subprocess.send(createStopIPCMessage());
            /*
             * However, even if subprocess doesn't react on the stop message,
             * it should be terminated after `options.timeoutMillis` milliseconds anyway.
             */
        }
        subprocess.disconnect();
    }
}
