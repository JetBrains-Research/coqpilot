export const consoleLoggingIsMuted = false;

export type LogColor = "red" | "green" | "blue" | "magenta" | "reset";

export function consoleLog(
    message: string,
    color: LogColor | undefined = undefined
) {
    if (consoleLoggingIsMuted) {
        return;
    }
    if (!color) {
        console.log(message);
        return;
    }
    const resetCode = code("reset");
    const colorCode = code(color);
    console.log(`${colorCode}%s${resetCode}`, message);
}

export function code(color: LogColor): string {
    if (color === "reset") {
        return "\x1b[0m";
    }
    if (color === "red") {
        return "\x1b[31m";
    }
    if (color === "green") {
        return "\x1b[32m";
    }
    if (color === "blue") {
        return "\x1b[34m";
    }
    if (color === "magenta") {
        return "\x1b[35m";
    }
    throw Error(`unknown LogColor: ${color}`);
}

export function consoleLogSeparatorLine(suffix: string = "") {
    consoleLog(`----------------------------${suffix}`);
}
