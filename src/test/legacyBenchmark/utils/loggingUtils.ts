import { LogColor, colorize } from "../../../utils/colorLogging";

export const consoleLoggingIsMuted = false;

export function consoleLog(message: string, color: LogColor = "default") {
    if (consoleLoggingIsMuted) {
        return;
    }
    console.log(colorize(message, color));
}

export function consoleLogSeparatorLine(suffix: string = "") {
    consoleLog(`----------------------------${suffix}`);
}
