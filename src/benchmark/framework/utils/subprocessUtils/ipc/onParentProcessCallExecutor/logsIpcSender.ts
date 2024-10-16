import { SeverityLevel } from "../../../../logging/benchmarkingLogger";
import { createLogIPCMessage } from "../ipcProtocol";

import { OnParentProcessCallExecutorUtils } from "./utils";

import Utils = OnParentProcessCallExecutorUtils;

export class LogsIPCSender {
    constructor(private readonly send: Utils.SenderFunction) {}

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
