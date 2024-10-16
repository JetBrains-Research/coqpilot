import { ValidateFunction } from "ajv";

import { failedAjvValidatorErrorsAsString } from "../../../../../../utils/ajvErrorsHandling";
import { stringifyAnyValue } from "../../../../../../utils/printers";
import { PromiseExecutor } from "../../../asyncUtils/promiseUtils";
import { IPCError } from "../ipcError";
import { IPCMessage, createIPCErrorIPCMessage } from "../ipcProtocol";

export namespace OnParentProcessCallExecutorUtils {
    export type SenderFunction = (message: any) => void;

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
