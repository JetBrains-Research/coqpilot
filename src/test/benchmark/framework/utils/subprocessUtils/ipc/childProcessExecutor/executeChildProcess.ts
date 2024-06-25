import { JSONSchemaType } from "ajv";
import * as child from "child_process";

import {
    time,
    timeToMillis,
} from "../../../../../../../llm/llmServices/utils/time";

import { stringifyAnyValue } from "../../../../../../../utils/printers";
import {
    BenchmarkingLogger,
    SeverityLevel,
} from "../../../../logging/benchmarkingLogger";
import { PromiseExecutor } from "../../../promiseUtils";
import {
    ExecutionErrorIPCMessage,
    IPCErrorIPCMessage,
    IPCMessage,
    IPCMessageSchemaValidators,
    LogIPCMessage,
    ResultIPCMessage,
    compileIPCMessageSchemas,
    createArgsIPCMessage,
} from "../ipcProtocol";

import {
    ExecutionResult,
    FailedExecution,
    SuccessfullExecution,
} from "./executionResult";
import { ChildProcessExecutorUtils } from "./utils";

import Utils = ChildProcessExecutorUtils;

export interface CommandToExecute {
    command: string;
    args: string[];
}

/**
 * To support more options, check: https://nodejs.org/api/child_process.html#child_processspawncommand-args-options.
 */
export interface ChildProcessOptions {
    workingDirectory?: string;

    /**
     * If undefined, `defaultChildProcessTimeoutMillis` timeout will be set.
     */
    timeoutMillis?: number;
}

export const defaultChildProcessTimeoutMillis = timeToMillis(
    time(10, "minute")
);

// TODO: document invariants
export async function executeProcessAsFunction<
    ArgsType extends child.Serializable,
    ResultType extends child.Serializable,
    T,
>(
    commandToExecute: CommandToExecute,
    args: ArgsType,
    argsSchema: JSONSchemaType<ArgsType>,
    resultSchema: JSONSchemaType<ResultType>,
    resultMapper: (result: ResultType) => T,
    options: ChildProcessOptions,
    benchmarkingLogger: BenchmarkingLogger,
    enableProcessLifetimeDebugLogs: boolean = false
): Promise<ExecutionResult<T>> {
    return new Promise((resolve, reject) => {
        const promiseExecutor: PromiseExecutor<ExecutionResult<T>> = {
            resolve: resolve,
            reject: reject,
        };
        const executionLogger =
            benchmarkingLogger.createChildLoggerWithIdentifier(
                [
                    "[",
                    `- commandToExecute: "${[commandToExecute.command, ...commandToExecute.args].join(" ")}"`,
                    `- args: ${stringifyAnyValue(args)}`,
                    `- workindDirectory: ${options.workingDirectory}`,
                    `- timeout: ${options.timeoutMillis} ms`,
                    "]",
                ].join("\n")
            );
        const lifetime: Utils.LifetimeObjects<ResultType, T> = {
            subprocess: undefined,
            executionLogger: executionLogger,
            enableProcessLifetimeDebugLogs: enableProcessLifetimeDebugLogs,
            promiseExecutor: promiseExecutor,
            resultMapper: resultMapper,
            debug: Utils.buildDebugExecutionLoggerShortcut(
                executionLogger,
                enableProcessLifetimeDebugLogs
            ),
            hasFinished: false,
        };

        try {
            lifetime.subprocess = child.spawn(
                commandToExecute.command,
                commandToExecute.args,
                createSpawnOptions(options)
            );
        } catch (e) {
            const error = e as Error;
            return Utils.rejectOnIPCError(
                `failed to spawn a child process (${error !== null ? error.message : stringifyAnyValue(error)})`,
                lifetime
            );
        }

        registerEventListeners<ArgsType, ResultType, T>(
            lifetime,
            argsSchema,
            resultSchema
        );

        const argsSent = lifetime.subprocess.send(createArgsIPCMessage(args));
        if (!argsSent) {
            return Utils.rejectOnIPCError(
                `failed to send arguments to the child process (IPC channel is closed or messages buffer is full)`,
                lifetime
            );
        }
    });
}

function createSpawnOptions(
    options: ChildProcessOptions
): child.CommonSpawnOptions {
    const spawnOptions: child.CommonSpawnOptions = {
        stdio: ["ignore", "ignore", "ignore", "ipc"],
        // shell: true // TODO: is it needed?
    };
    if (options.workingDirectory !== undefined) {
        spawnOptions.cwd = options.workingDirectory;
    }
    spawnOptions.timeout =
        options.timeoutMillis === undefined
            ? defaultChildProcessTimeoutMillis
            : options.timeoutMillis;
    return spawnOptions;
}

function registerEventListeners<ArgsType, ResultType, T>(
    lifetime: Utils.LifetimeObjects<ResultType, T>,
    argsSchema: JSONSchemaType<ArgsType>,
    resultSchema: JSONSchemaType<ResultType>
) {
    const ipcMessageValidators = compileIPCMessageSchemas(
        argsSchema,
        resultSchema
    );
    const subprocess = lifetime.subprocess!;

    // Is triggered right after subprocess is spawned successfully.
    subprocess.on("spawn", () =>
        lifetime.debug("Child process was successfully spawned")
    );

    // Is triggered after subprocess calls `process.send()`.
    subprocess.on("message", (message) =>
        onMessageReceived(message, ipcMessageValidators, lifetime)
    );

    /*
     * Is triggered if one of the following errors occurred:
     * subprocess could not be spawned / subprocess could not be killed / sending message failed / subprocess was aborted.
     * Note: exit event might not fire afterwards.
     */
    subprocess.on("error", (error) => {
        if (lifetime.hasFinished) {
            lifetime.debug(
                `Inter-process-communication error occurred on child process finish: ${error.message}`
            );
        } else {
            Utils.rejectOnIPCError(error.message, lifetime);
        }
    });

    // Is triggered once the parent process or the child process called `disconnect` (closes IPC channel).
    subprocess.on("disconnect", () =>
        lifetime.debug("Child process was disconnected: IPC channel closed")
    );

    /*
     * Is triggered after the subprocess finishes its work (but in the case of `error`, might not be fired).
     * However, resources might not be cleaned at this point.
     */
    subprocess.on("exit", (exitCodeOrNull, signalOrNull) => {
        const exitedWith =
            exitCodeOrNull === null
                ? `signal ${signalOrNull}`
                : `code ${exitCodeOrNull}`;
        lifetime.debug(`Child process exited with ${exitedWith}`);
    });

    /**
     * Is triggered after the subprocess is fully closed, i.e. its resources are free (IPC channel is closed).
     */
    subprocess.on("close", (exitCodeOrNull, signalOrNull) => {
        const withExitCode =
            exitCodeOrNull === null
                ? "no exit code"
                : `with exit code ${exitCodeOrNull}`;
        const withSignal =
            signalOrNull === null ? "no signal" : `with signal ${signalOrNull}`;
        lifetime.debug(
            `Child process completely finished, its resources are free: ${withExitCode}, ${withSignal}`
        );
        // TODO: maybe add a delay here (?)
        // TODO: read child process logs from its file
        Utils.rejectOnIPCError(
            "Child process finished silently before sending result: communication error",
            lifetime
        );
    });
}

function onMessageReceived<ArgsType, ResultType, T>(
    message: child.Serializable,
    ipcMessageValidators: IPCMessageSchemaValidators<ArgsType, ResultType>,
    lifetime: Utils.LifetimeObjects<ResultType, T>
) {
    const ipcMessage = message as IPCMessage;
    if (!ipcMessageValidators.validateIPCMessage(ipcMessage)) {
        return Utils.rejectOnInvalidIPCMessageSchemaError(
            "",
            ipcMessage,
            ipcMessageValidators.validateIPCMessage,
            lifetime
        );
    }

    switch (ipcMessage.messageType) {
        case "result":
            const resultMessage = message as ResultIPCMessage<ResultType>;
            if (!ipcMessageValidators.validateResultMessage(resultMessage)) {
                return Utils.rejectOnInvalidIPCMessageSchemaError(
                    "result",
                    resultMessage,
                    ipcMessageValidators.validateResultMessage,
                    lifetime
                );
            }
            lifetime.debug(
                "Successfully received execution result from the child process"
            );
            Utils.finishSubprocess(lifetime);
            return lifetime.promiseExecutor.resolve(
                new SuccessfullExecution(
                    lifetime.resultMapper(resultMessage.result)
                )
            );

        case "execution-error":
            const executionErrorMessage = message as ExecutionErrorIPCMessage;
            if (
                !ipcMessageValidators.validateExecutionErrorMessage(
                    executionErrorMessage
                )
            ) {
                return Utils.rejectOnInvalidIPCMessageSchemaError(
                    "execution error",
                    executionErrorMessage,
                    ipcMessageValidators.validateExecutionErrorMessage,
                    lifetime
                );
            }
            lifetime.debug(
                `Error occurred during execution in the child process: "${executionErrorMessage.errorTypeName}: ${executionErrorMessage.errorMessage}"`
            );
            Utils.finishSubprocess(lifetime);
            return lifetime.promiseExecutor.resolve(
                new FailedExecution(
                    executionErrorMessage.errorTypeName,
                    executionErrorMessage.errorMessage
                )
            );

        case "ipc-error":
            const ipcErrorMessage = message as IPCErrorIPCMessage;
            if (
                !ipcMessageValidators.validateIPCErrorMessage(ipcErrorMessage)
            ) {
                return Utils.rejectOnInvalidIPCMessageSchemaError(
                    "IPC error",
                    ipcErrorMessage,
                    ipcMessageValidators.validateIPCErrorMessage,
                    lifetime
                );
            }
            return Utils.rejectOnIPCError(
                ipcErrorMessage.errorMessage,
                lifetime
            );

        case "log":
            const logMessage = message as LogIPCMessage;
            if (!ipcMessageValidators.validateLogMessage(logMessage)) {
                return Utils.rejectOnInvalidIPCMessageSchemaError(
                    "log",
                    logMessage,
                    ipcMessageValidators.validateLogMessage,
                    lifetime
                );
            }
            switch (logMessage.severityLevel) {
                case SeverityLevel.ERROR:
                    lifetime.executionLogger.error(logMessage.logMessage);
                    break;
                case SeverityLevel.INFO:
                    lifetime.executionLogger.info(logMessage.logMessage);
                    break;
                case SeverityLevel.DEBUG:
                    lifetime.executionLogger.debug(logMessage.logMessage);
                    break;
            }
            return;

        default:
            return Utils.rejectOnIPCError(
                `child process sent message of unexpected "${ipcMessage.messageType}" type: ${stringifyAnyValue(ipcMessage)}`,
                lifetime
            );
    }
}
