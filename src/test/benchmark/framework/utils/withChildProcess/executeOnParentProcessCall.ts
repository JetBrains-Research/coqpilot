import { JSONSchemaType, ValidateFunction } from "ajv";

import { failedAjvValidatorErrorsAsString } from "../../../../../utils/ajvErrorsHandling";
import { stringifyAnyValue } from "../../../../../utils/printers";
import { SeverityLevel } from "../../logging/benchmarkingLogger";

import {
    ArgsIPCMessage,
    IPCError,
    IPCMessage,
    compileIPCMessageSchemas,
    createExecutionErrorIPCMessage,
    createIPCErrorIPCMessage,
    createLogIPCMessage,
    createResultIPCMessage,
} from "./ipcProtocol";
import { PromiseExecutor } from "./processExecutionUtils";

// TODO: document
export async function executeAsFunctionOnParentProcessCall<
    ArgsType,
    ResultType,
>(
    argsSchema: JSONSchemaType<ArgsType>,
    resultSchema: JSONSchemaType<ResultType>,
    body: (args: ArgsType, logger: LogsIPCSender) => Promise<ResultType>
) {
    return new Promise((resolve, reject) => {
        const promiseExecutor: PromiseExecutor<void> = {
            resolve: resolve,
            reject: reject,
        };
        const send = process.send;
        if (!process.connected) {
            return reject(
                new IPCError(
                    "this child process is not connected to the parent process via an IPC channel"
                )
            );
        } else if (send === undefined) {
            return reject(
                new IPCError(
                    "invariant failed: `process.connected` was true, but `process.send` is undefined"
                )
            );
        }
        const lifetime: LifetimeObjects = {
            promiseExecutor: promiseExecutor,
            send: send,
        };
        const ipcMessageValidators = compileIPCMessageSchemas(
            argsSchema,
            resultSchema
        );

        process.on("message", async (message) => {
            const ipcMessage = message as IPCMessage;
            if (!ipcMessageValidators.validateIPCMessage(ipcMessage)) {
                return handleInvalidIPCMessageSchemaError(
                    "",
                    ipcMessage,
                    ipcMessageValidators.validateIPCMessage,
                    lifetime
                );
            }

            switch (ipcMessage.messageType) {
                case "args":
                    const argsMessage = message as ArgsIPCMessage<ArgsType>;
                    if (
                        !ipcMessageValidators.validateArgsMessage(argsMessage)
                    ) {
                        return handleInvalidIPCMessageSchemaError(
                            "args",
                            argsMessage,
                            ipcMessageValidators.validateArgsMessage,
                            lifetime
                        );
                    }
                    return await executeBodyAndSendResult(
                        body,
                        argsMessage.args,
                        lifetime
                    );
                case "stop":
                    return lifetime.promiseExecutor.resolve();
                default:
                    return tryToReportIPCErrorToParentAndThrow(
                        `parent process sent message of unexpected "${ipcMessage.messageType}" type: ${stringifyAnyValue(ipcMessage)}`,
                        lifetime
                    );
            }
        });
    });
}

export type SenderFunction = (message: any) => boolean;

export class LogsIPCSender {
    constructor(private readonly send: SenderFunction) {}

    error(message: string) {
        this.sendLog(SeverityLevel.ERROR, message);
    }

    info(message: string) {
        this.sendLog(SeverityLevel.INFO, message);
    }

    debug(message: string) {
        this.sendLog(SeverityLevel.DEBUG, message);
    }

    private sendLog(severity: SeverityLevel, message: string) {
        this.send(createLogIPCMessage(message, severity));
    }
}

interface LifetimeObjects {
    promiseExecutor: PromiseExecutor<void>;
    send: SenderFunction;
}

async function executeBodyAndSendResult<ArgsType, ResultType>(
    body: (args: ArgsType, logger: LogsIPCSender) => Promise<ResultType>,
    args: ArgsType,
    lifetime: LifetimeObjects
) {
    const logger = new LogsIPCSender(lifetime.send);
    let result: ResultType;
    try {
        result = await body(args, logger);
    } catch (e) {
        const error = e as Error;
        lifetime.send(
            createExecutionErrorIPCMessage(
                error !== null ? error.message : stringifyAnyValue(e),
                error !== null ? error.name : undefined
            )
        );
        return lifetime.promiseExecutor.resolve();
    }
    const resultSent = lifetime.send(createResultIPCMessage(result));
    if (!resultSent) {
        return tryToReportIPCErrorToParentAndThrow(
            `failed to send execution result to the parent process (IPC channel is closed or messages buffer is full)`,
            lifetime
        );
    }
}

function tryToReportIPCErrorToParentAndThrow(
    errorMessage: string,
    lifetime: LifetimeObjects
) {
    lifetime.send(createIPCErrorIPCMessage(errorMessage)); // it's okay if it fails for some reason
    lifetime.promiseExecutor.reject(new IPCError(errorMessage));
}

function handleInvalidIPCMessageSchemaError<T extends IPCMessage>(
    ipcMessageTypeName: string,
    ipcMessage: T,
    failedValidator: ValidateFunction<T>,
    lifetime: LifetimeObjects
) {
    tryToReportIPCErrorToParentAndThrow(
        [
            `received IPC ${ipcMessageTypeName}${ipcMessageTypeName === "" ? "" : " "}message `,
            `of invalid structure ${stringifyAnyValue(ipcMessage)}: `,
            `${failedAjvValidatorErrorsAsString(failedValidator)}`,
        ].join(""),
        lifetime
    );
}
