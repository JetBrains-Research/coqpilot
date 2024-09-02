import { ValidateFunction } from "ajv";
import * as child from "child_process";
import ipc from "node-ipc";

import { failedAjvValidatorErrorsAsString } from "../../../../../../utils/ajvErrorsHandling";
import { stringifyAnyValue } from "../../../../../../utils/printers";
import { BenchmarkingLogger } from "../../../../logging/benchmarkingLogger";
import { PromiseExecutor } from "../../../asyncUtils/promiseUtils";
import { IPCError } from "../ipcError";
import { IPCMessage, createStopIPCMessage } from "../ipcProtocol";

import { ExecutionResult } from "./executionResult";

export namespace ChildProcessExecutorUtils {
    export type IPCSocket = any;

    export interface LifetimeObjects<ResultType, T> {
        subprocess: child.ChildProcess | undefined;
        executionLogger: BenchmarkingLogger;
        enableProcessLifetimeDebugLogs: boolean;
        promiseExecutor: PromiseExecutor<ExecutionResult<T>>;
        resultMapper: (result: ResultType) => T;
        send: (socket: IPCSocket, message: child.Serializable) => void;
        debug: ConditionalExecutionLoggerDebug;
        hasFinished: boolean;
    }

    export type ConditionalExecutionLoggerDebug = (message: string) => void;

    export function stopIPCServer(lifetime: LifetimeObjects<any, any>) {
        ipc.server.stop();
        lifetime.debug("Parent process stopped the IPC server");
    }

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
        socket: IPCSocket | undefined,
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        const asOneRecord = lifetime.executionLogger.asOneRecord();
        asOneRecord.error(
            "Process execution failed due to inter-process-communication error"
        );
        if (lifetime.enableProcessLifetimeDebugLogs) {
            asOneRecord.debug(`Cause: ${errorMessage}`);
        }
        finishSubprocess(socket, lifetime);
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
        socket: IPCSocket | undefined,
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        rejectOnIPCError(
            [
                `received IPC ${ipcMessageTypeName}${ipcMessageTypeName === "" ? "" : " "}message `,
                `of invalid structure ${stringifyAnyValue(ipcMessage)}: `,
                `${failedAjvValidatorErrorsAsString(failedValidator)}`,
            ].join(""),
            socket,
            lifetime
        );
    }

    export function finishSubprocess<ResultType, T>(
        socket: IPCSocket | undefined,
        lifetime: LifetimeObjects<ResultType, T>
    ) {
        if (lifetime.hasFinished) {
            return;
        }
        lifetime.hasFinished = true;

        const subprocess = lifetime.subprocess;
        if (subprocess === undefined) {
            return;
        }
        if (subprocess.exitCode === null) {
            if (socket !== undefined) {
                /*
                 * Subprocess is still running, it's needed to be stopped.
                 * Note: we don't try to send a signal to the subprocess,
                 * because it doesn't give any guarantees on subprocess termination and
                 * it may cause undefined behaviour (if the subprocess already exited and
                 * another process with the same PID receives this signal).
                 */
                lifetime.send(socket, createStopIPCMessage()); // TODO: add try-catch here?
                /*
                 * However, even if subprocess doesn't react on the stop message,
                 * it should be terminated after `options.timeoutMillis` milliseconds anyway.
                 */
            }
        }
        if (subprocess.connected) {
            subprocess.disconnect();
        }
        lifetime.debug("Parent process finished subprocess");

        stopIPCServer(lifetime);
    }
}
