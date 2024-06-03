import * as child from "child_process";

import { ErrorWithCause } from "../../../../../utils/errorsUtils";
import { stringifyAnyValue } from "../../../../../utils/printers";
import {
    BenchmarkingLogger,
    SeverityLevel,
} from "../../logging/benchmarkingLogger";

export async function spawnProcess() {}

export async function spawnProcessInNixEnvironment() {}

/**
 * To support more options, check: https://nodejs.org/api/child_process.html#child_processspawncommand-args-options.
 */
export interface ChildProcessOptions {
    workingDirectory?: string;
    timeoutMillis?: number;
}

export class InternalChildProcessError extends ErrorWithCause {}

export interface OnChildProcessEvents {
    onDataReceived: (data: any) => void;
    onErrorOccurred: (error: Error) => void;
    onLogReceived: (severity: SeverityLevel, message: string) => void;
    onInternalErrorOccurred: (error: InternalChildProcessError) => void;
}

type IPCMessageType =
    | "data"
    | "error"
    | "internal-error"
    | "log.error"
    | "log.info"
    | "log.debug";

interface IPCMessage {
    messageType: IPCMessageType;
    data: any;
}

interface RequestedPromise<T> {
    resolve: (value: T | PromiseLike<T>) => void;
    reject: (reason?: any) => void;
}

// TODO: design process finishing
// afterwards, it might be possible to get rid of classes

// TODO: always check `send` return value to be true!
// TODO: check for `connected` at the very beginning?

/**
 * Represents and handles an actual child process.
 *
 * The actual child process is created with its `stdin`, `stdout` and `stderr` set to `/dev/null`.
 * However, the child process is able to send data, perform logging and throw errors:
 * all information will be wrapped and sent to the parent process via an IPC channel.
 */
export class AbstractChildProcess {
    private readonly subprocess: child.ChildProcess;

    // TODO: add finish child process condition, being checked on each event
    // if true =>
    // 1. call disconnect()
    // 2. wait (?) for close event / exitCode (null if it's still running) property
    // 3. maybe kill() if it doesn't stop

    /**
     * Creates `ChildProcess` and spawns an actual child process handled by this `ChildProcess`.
     */
    constructor(
        command: string,
        args: string[],
        options: ChildProcessOptions,
        protected readonly onChildProcessEvents: OnChildProcessEvents,
        protected readonly requestedPromise?: RequestedPromise<any>
    ) {
        this.subprocess = child.spawn(
            command,
            args,
            AbstractChildProcess.createSpawnOptions(options)
        );
        this.registerEventListeners();
    }

    // TODO: when internal error (error?) occurred, finish process and reject result promise
    // TODO: support debug logging for each internal event by flag

    private static createSpawnOptions(
        options: ChildProcessOptions
    ): child.CommonSpawnOptions {
        const spawnOptions: child.CommonSpawnOptions = {
            stdio: ["ignore", "ignore", "ignore", "ipc"],
            // shell: true // TODO: is it needed?
        };
        if (options.workingDirectory !== undefined) {
            spawnOptions.cwd = options.workingDirectory;
        }
        if (options.timeoutMillis !== undefined) {
            spawnOptions.timeout = options.timeoutMillis;
        }
        return spawnOptions;
    }

    private registerEventListeners() {
        // Is triggered right after subprocess is spawned successfully.
        this.subprocess.on("spawn", () => {
            // TODO: log
        });

        // Is triggered after subprocess calls `process.send()`.
        this.subprocess.on("message", (message) => {
            const ipcMessage = message as IPCMessage;
            // TODO: validate received message via Ajv schema (rework types validation below too)
            if (ipcMessage === null) {
                return this.onChildProcessEvents.onInternalErrorOccurred(
                    new InternalChildProcessError(
                        `received IPC message of invalid structure: ${stringifyAnyValue(ipcMessage)}`
                    )
                );
            }
            switch (ipcMessage.messageType) {
                case "data":
                    return this.onChildProcessEvents.onDataReceived(
                        ipcMessage.data
                    );
                case "error":
                    const errorMessage = ipcMessage.data as string;
                    if (errorMessage === null) {
                        return this.onChildProcessEvents.onInternalErrorOccurred(
                            new InternalChildProcessError(
                                `received IPC message of invalid structure: ${stringifyAnyValue(ipcMessage)}`
                            )
                        );
                    }
                    return this.onChildProcessEvents.onErrorOccurred(
                        Error(errorMessage)
                    );
                case "internal-error":
                    const internalErrorMessage = ipcMessage.data as string;
                    if (internalErrorMessage === null) {
                        return this.onChildProcessEvents.onInternalErrorOccurred(
                            new InternalChildProcessError(
                                `received IPC message of invalid structure: ${stringifyAnyValue(ipcMessage)}`
                            )
                        );
                    }
                    return this.onChildProcessEvents.onInternalErrorOccurred(
                        new InternalChildProcessError(internalErrorMessage)
                    );
                case "log.error":
                    return this.handleLogIPCMessage(
                        SeverityLevel.ERROR,
                        ipcMessage
                    );
                case "log.info":
                    return this.handleLogIPCMessage(
                        SeverityLevel.INFO,
                        ipcMessage
                    );
                case "log.debug":
                    return this.handleLogIPCMessage(
                        SeverityLevel.DEBUG,
                        ipcMessage
                    );
            }
        });

        /*
         * Is triggered if one of the following errors occurred:
         * subprocess could not be spawned / subprocess could not be killed / sending message failed / subprocess was aborted.
         * Note: exit event might not fire afterwards.
         */
        this.subprocess.on("error", (error) => {
            this.onChildProcessEvents.onInternalErrorOccurred(
                new InternalChildProcessError(undefined, error)
            );
        });

        // Is triggered once the parent process or the child process called `disconnect` (closes IPC channel).
        this.subprocess.on("disconnect", () => {
            // TODO: log
        });

        /*
         * Is triggered after the subprocess finishes its work (but in the case of `error`, might not be fired).
         * However, resources might not be cleaned at this point.
         */
        this.subprocess.on("exit", (exitCodeOrNull, signalOrNull) => {
            // TODO: log
        });

        /**
         * Is triggered after the subprocess is fully closed, i.e. its resources are free (IPC channel is closed).
         */
        this.subprocess.on("close", (exitCode, signalOrNull) => {
            // TODO: log
        });
    }

    private handleLogIPCMessage(
        logSeverity: SeverityLevel,
        ipcMessage: IPCMessage
    ) {
        const logMessage = ipcMessage.data as string;
        if (logMessage === null) {
            return this.onChildProcessEvents.onInternalErrorOccurred(
                new InternalChildProcessError(
                    `received IPC message of invalid structure: ${stringifyAnyValue(ipcMessage)}`
                )
            );
        }
        return this.onChildProcessEvents.onLogReceived(logSeverity, logMessage);
    }
}

export class ChildProcessFunction<T> extends AbstractChildProcess {
    // TODO: specify Ajv schema to validate resulting object
    constructor(
        command: string,
        args: string[],
        options: ChildProcessOptions,
        benchmarkingLogger: BenchmarkingLogger,
        requestedPromise: RequestedPromise<T>
    ) {
        super(
            command,
            args,
            options,
            {
                onDataReceived: (data) => {
                    const result = data as T;
                    if (result === null) {
                        return this.onChildProcessEvents.onInternalErrorOccurred(
                            new InternalChildProcessError(
                                `received data is not of valid result type: ${stringifyAnyValue(data)}`
                            )
                        );
                    }
                    requestedPromise.resolve(result);
                },
                // TODO: onLogs, onError: log with logger and reject / resolve with error value
            } as OnChildProcessEvents,
            requestedPromise
        );
    }
}

export abstract class ExecutionResult<T> {
    constructor(readonly maybeResult: T | undefined) {}
}

export class SuccessfullExecution<T> extends ExecutionResult<T> {
    constructor(readonly result: T) {
        super(result);
    }
}

export class FailedExecution<T> extends ExecutionResult<T> {
    constructor(readonly failureCause: string) {
        super(undefined);
    }
}

export async function executeProcessAsFunction<T>(
    command: string,
    args: string[],
    options: ChildProcessOptions,
    benchmarkingLogger: BenchmarkingLogger
): Promise<ExecutionResult<T>> {
    return new Promise((resolve, reject) => {
        new ChildProcessFunction(command, args, options, benchmarkingLogger, {
            resolve: resolve,
            reject: reject,
        });
    });
}

function createIPCMessage(messageType: IPCMessageType, data: any): IPCMessage {
    return {
        messageType: messageType,
        data: data,
    };
}

export async function executeAsFunctionOnParentProcessCall<
    ArgsType,
    ResultType,
>(
    // TODO: provide logger with logs being sent to parent
    body: (args: ArgsType) => Promise<ResultType>
) {
    const send = process.send;
    if (!process.connected) {
        throw new InternalChildProcessError(
            "this child process is not connected to the parent process via an IPC channel"
        );
    } else if (send === undefined) {
        throw new InternalChildProcessError(
            "invariant failed: `process.connected` was true, but `process.send` is undefined"
        );
    }
    // By protocol, the parent process sends function argument as `ArgsType`.
    process.on("message", async (ipcMessage) => {
        // TODO: check type with Ajv schema
        const args = ipcMessage as ArgsType;
        if (args === null) {
            return send(
                createIPCMessage(
                    "internal-error",
                    `received message is not of valid args type: ${stringifyAnyValue(ipcMessage)}`
                )
            );
        }
        try {
            // TODO: check whether it will be awaited or not
            const result = await body(args);
            return send(createIPCMessage("data", result));
        } catch (e) {
            const error = e as Error;
            return send(
                createIPCMessage(
                    "error",
                    error !== null ? error.message : stringifyAnyValue(error)
                )
            );
        }
    });
}
