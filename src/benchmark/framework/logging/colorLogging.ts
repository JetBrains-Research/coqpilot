export type LogColor = "red" | "green" | "blue" | "magenta" | "gray" | "reset";

export function colorize(text: string, color: LogColor | undefined): string {
    if (color === undefined) {
        return text;
    }
    const resetCode = code("reset");
    const colorCode = code(color);
    return `${colorCode}${text}${resetCode}`;
}

export function code(color: LogColor): string {
    switch (color) {
        case "reset":
            return "\x1b[0m";
        case "red":
            return "\x1b[31m";
        case "green":
            return "\x1b[32m";
        case "blue":
            return "\x1b[34m";
        case "magenta":
            return "\x1b[35m";
        case "gray":
            return "\x1b[90m";
    }
}
