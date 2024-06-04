import { ValidateFunction } from "ajv";

import { failedAjvValidatorErrorsAsString } from "../../../../../../../utils/ajvErrorsHandling";
import { stringifyAnyValue } from "../../../../../../../utils/printers";
import { PromiseExecutor } from "../../commonUtils";
import { IPCError } from "../ipcError";
import { IPCMessage, createIPCErrorIPCMessage } from "../ipcProtocol";

import { SenderFunction } from "./executeOnParentProcessCall";

export namespace OnParentProcessCallExecutorUtils {
    export interface LifetimeObjects {
        promiseExecutor: PromiseExecutor<void>;
        send: SenderFunction;
    }

    export function tryToReportIPCErrorToParentAndThrow(
        errorMessage: string,
        lifetime: LifetimeObjects
    ) {
        lifetime.send(createIPCErrorIPCMessage(errorMessage)); // it's okay if it fails for some reason
        lifetime.promiseExecutor.reject(new IPCError(errorMessage));
    }

    export function handleInvalidIPCMessageSchemaError<T extends IPCMessage>(
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
}
