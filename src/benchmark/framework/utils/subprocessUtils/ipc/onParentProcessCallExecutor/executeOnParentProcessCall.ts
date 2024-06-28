import { JSONSchemaType } from "ajv";
import ipc from "node-ipc";

import { stringifyAnyValue } from "../../../../../../utils/printers";
import { PromiseExecutor } from "../../../promiseUtils";
import {
    ArgsIPCMessage,
    IPCMessage,
    IPCMessageSchemaValidators,
    IPC_APPSPACE_KEYWORD,
    IPC_MESSAGE_KEYWORD,
    compileIPCMessageSchemas,
    createExecutionErrorIPCMessage,
    createResultIPCMessage,
} from "../ipcProtocol";

import { LogsIPCSender } from "./logsIpcSender";
import { OnParentProcessCallExecutorUtils } from "./utils";

import Utils = OnParentProcessCallExecutorUtils;

// TODO: document
// TODO: design better logging through actual file
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
        const lifetime: Utils.LifetimeObjects = {
            promiseExecutor: promiseExecutor,
            send: (message) =>
                ipc.of.coqpilot.emit(IPC_MESSAGE_KEYWORD, message),
        };
        connectAsIPCClient(lifetime, body, argsSchema, resultSchema);
    });
}

function connectAsIPCClient<ArgsType, ResultType>(
    lifetime: Utils.LifetimeObjects,
    body: (args: ArgsType, logger: LogsIPCSender) => Promise<ResultType>,
    argsSchema: JSONSchemaType<ArgsType>,
    resultSchema: JSONSchemaType<ResultType>
) {
    const ipcMessageValidators = compileIPCMessageSchemas(
        argsSchema,
        resultSchema
    );

    // TODO: set up ipc config better
    ipc.config.appspace = IPC_APPSPACE_KEYWORD;
    ipc.config.id = "coqpilot-ipc-client"; // TODO: is it needed at all?
    ipc.config.retry = 1000;
    ipc.config.silent = true;

    // TODO: find the way to call `ipc.of` by parameterized id
    ipc.connectTo("coqpilot", function () {
        ipc.of.coqpilot.on("connect", function () {
            console.error("connected to the IPC server of the parent process");
            // TODO: maybe add first "hello" from the child process?
            lifetime.send("hello");
        });
        ipc.of.coqpilot.on("disconnect", function () {
            console.error(
                "disconnected from the IPC server of the parent process"
            );
        });
        ipc.of.coqpilot.on(IPC_MESSAGE_KEYWORD, async (data) => {
            // TODO: is `await` needed here?
            const actualMessage =
                data?.message === undefined ? data : data.message;
            await onMessageReceived(
                actualMessage,
                ipcMessageValidators,
                lifetime,
                body
            );
        });
    });
}

async function onMessageReceived<ArgsType, ResultType>(
    message: any,
    ipcMessageValidators: IPCMessageSchemaValidators<ArgsType, ResultType>,
    lifetime: Utils.LifetimeObjects,
    body: (args: ArgsType, logger: LogsIPCSender) => Promise<ResultType>
) {
    const ipcMessage = message as IPCMessage;
    if (!ipcMessageValidators.validateIPCMessage(ipcMessage)) {
        return Utils.handleInvalidIPCMessageSchemaError(
            "",
            ipcMessage,
            ipcMessageValidators.validateIPCMessage,
            lifetime
        );
    }

    switch (ipcMessage.messageType) {
        case "args":
            const argsMessage = message as ArgsIPCMessage<ArgsType>;
            if (!ipcMessageValidators.validateArgsMessage(argsMessage)) {
                return Utils.handleInvalidIPCMessageSchemaError(
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
            return Utils.tryToReportIPCErrorToParentAndThrow(
                `parent process sent message of unexpected "${ipcMessage.messageType}" type: ${stringifyAnyValue(ipcMessage)}`,
                lifetime
            );
    }
}

async function executeBodyAndSendResult<ArgsType, ResultType>(
    body: (args: ArgsType, logger: LogsIPCSender) => Promise<ResultType>,
    args: ArgsType,
    lifetime: Utils.LifetimeObjects
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

    try {
        lifetime.send(createResultIPCMessage(result));
    } catch (e) {
        // TODO: move to utils
        const error = e as Error;
        const errorMessage =
            error !== null ? error.message : stringifyAnyValue(e);
        return Utils.tryToReportIPCErrorToParentAndThrow(
            `failed to send execution result to the parent process: ${errorMessage}`,
            lifetime
        );
    }
}
