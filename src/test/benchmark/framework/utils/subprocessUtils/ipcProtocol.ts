import { JSONSchemaType, ValidateFunction } from "ajv";

import { AjvMode, buildAjv } from "../../../../../utils/ajvErrorsHandling";
import { SeverityLevel } from "../../logging/benchmarkingLogger";

export type IPCMessageType =
    | "args"
    | "result"
    | "execution-error"
    | "ipc-error"
    | "log"
    | "stop";

export interface IPCMessage {
    messageType: IPCMessageType;
}

export interface ArgsIPCMessage<T> extends IPCMessage {
    messageType: "args";
    args: T;
}

export function createArgsIPCMessage<T>(args: T): ArgsIPCMessage<T> {
    return {
        messageType: "args",
        args: args,
    };
}

export interface ResultIPCMessage<T> extends IPCMessage {
    messageType: "result";
    result: T;
}

export function createResultIPCMessage<T>(result: T): ResultIPCMessage<T> {
    return {
        messageType: "result",
        result: result,
    };
}

export interface ExecutionErrorIPCMessage extends IPCMessage {
    messageType: "execution-error";
    errorMessage: string;
    errorTypeName?: string;
}

export function createExecutionErrorIPCMessage(
    errorMessage: string,
    errorTypeName?: string
): ExecutionErrorIPCMessage {
    return {
        messageType: "execution-error",
        errorMessage: errorMessage,
        errorTypeName: errorTypeName,
    };
}

export interface IPCErrorIPCMessage extends IPCMessage {
    messageType: "ipc-error";
    errorMessage: string;
}

export function createIPCErrorIPCMessage(
    errorMessage: string
): IPCErrorIPCMessage {
    return {
        messageType: "ipc-error",
        errorMessage: errorMessage,
    };
}

export interface LogIPCMessage extends IPCMessage {
    messageType: "log";
    logMessage: string;
    severityLevel: SeverityLevel;
}

export function createLogIPCMessage(
    logMessage: string,
    severityLevel: SeverityLevel
): LogIPCMessage {
    return {
        messageType: "log",
        logMessage: logMessage,
        severityLevel: severityLevel,
    };
}

export function createStopIPCMessage(): IPCMessage {
    return {
        messageType: "stop",
    };
}

export interface IPCMessageSchemaValidators<ArgsType, ResultType> {
    validateIPCMessage: ValidateFunction<IPCMessage>;
    validateArgsMessage: ValidateFunction<ArgsIPCMessage<ArgsType>>;
    validateResultMessage: ValidateFunction<ResultIPCMessage<ResultType>>;
    validateExecutionErrorMessage: ValidateFunction<ExecutionErrorIPCMessage>;
    validateIPCErrorMessage: ValidateFunction<IPCErrorIPCMessage>;
    validateLogMessage: ValidateFunction<LogIPCMessage>;
}

export function compileIPCMessageSchemas<ArgsType, ResultType>(
    argsSchema: JSONSchemaType<ArgsType>,
    resultSchema: JSONSchemaType<ResultType>
): IPCMessageSchemaValidators<ArgsType, ResultType> {
    const ajv = buildAjv(AjvMode.COLLECT_ALL_ERRORS);
    return {
        validateIPCMessage: ajv.compile(ipcMessageSchema),
        validateArgsMessage: ajv.compile(argsMessageSchema(argsSchema)),
        validateResultMessage: ajv.compile(resultMessageSchema(resultSchema)),
        validateExecutionErrorMessage: ajv.compile(executionErrorMessageSchema),
        validateIPCErrorMessage: ajv.compile(ipcErrorMessageSchema),
        validateLogMessage: ajv.compile(logMessageSchema),
    };
}

export const ipcMessageSchema: JSONSchemaType<IPCMessage> = {
    type: "object",
    properties: {
        messageType: {
            type: "string",
            enum: [
                "args",
                "result",
                "execution-error",
                "ipc-error",
                "log",
                "stop",
            ],
        },
    },
    required: ["messageType"],
    additionalProperties: true,
};

export function argsMessageSchema<T>(
    argsSchema: JSONSchemaType<T>
): JSONSchemaType<ArgsIPCMessage<T>> {
    return {
        type: "object",
        properties: {
            messageType: {
                type: "string",
                enum: ["args"],
            },
            args: {
                type: "object",
                oneOf: [argsSchema],
            },
        },
        required: ["messageType", "args"],
        additionalProperties: false,
    } as JSONSchemaType<ArgsIPCMessage<T>>;
}

export function resultMessageSchema<T>(
    resultSchema: JSONSchemaType<T>
): JSONSchemaType<ResultIPCMessage<T>> {
    return {
        type: "object",
        properties: {
            messageType: {
                type: "string",
                enum: ["result"],
            },
            result: {
                type: "object",
                oneOf: [resultSchema],
            },
        },
        required: ["messageType", "result"],
        additionalProperties: false,
    } as JSONSchemaType<ResultIPCMessage<T>>;
}

export const executionErrorMessageSchema: JSONSchemaType<ExecutionErrorIPCMessage> =
    {
        type: "object",
        properties: {
            messageType: {
                type: "string",
                enum: ["execution-error"],
            },
            errorMessage: {
                type: "string",
            },
            errorTypeName: {
                type: "string",
                nullable: true,
            },
        },
        required: ["messageType", "errorMessage"],
        additionalProperties: false,
    };

export const ipcErrorMessageSchema: JSONSchemaType<IPCErrorIPCMessage> = {
    type: "object",
    properties: {
        messageType: {
            type: "string",
            enum: ["ipc-error"],
        },
        errorMessage: {
            type: "string",
        },
    },
    required: ["messageType", "errorMessage"],
    additionalProperties: false,
};

export const logMessageSchema: JSONSchemaType<LogIPCMessage> = {
    type: "object",
    properties: {
        messageType: {
            type: "string",
            enum: ["log"],
        },
        logMessage: {
            type: "string",
        },
        severityLevel: {
            type: "number",
            enum: [0, 1, 2],
        },
    },
    required: ["messageType", "logMessage", "severityLevel"],
    additionalProperties: false,
};
