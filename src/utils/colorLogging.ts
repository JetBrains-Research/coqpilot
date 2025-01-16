import { illegalState } from "./throwErrors";

export type LogColor =
    | "default"
    | "red"
    | "green"
    | "yellow"
    | "blue"
    | "magenta"
    | "gray";

export function colorize(text: string, color: LogColor): string {
    if (color === "default") {
        return text;
    }
    const colorCode = code(color);
    return `${colorCode}${text}${resetCode}`;
}

export const resetCode = "\x1b[0m";

export function code(color: LogColor): string {
    switch (color) {
        case "default":
            illegalState(
                "default color does not have a code: it is just plain text"
            );
        case "red":
            return "\x1b[31m";
        case "green":
            return "\x1b[32m";
        case "yellow":
            return "\x1b[33m";
        case "blue":
            return "\x1b[34m";
        case "magenta":
            return "\x1b[35m";
        case "gray":
            return "\x1b[90m";
    }
}
