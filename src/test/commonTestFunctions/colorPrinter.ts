export type Color = "red" | "green" | "yellow" | "blue" | "magenta" | "reset";

export function color(text: string, color: Color): string {
    return `${code(color)}${text}${code("reset")}`;
}
function code(color: Color): string {
    if (color === "reset") {
        return "\x1b[0m";
    }
    if (color === "red") {
        return "\x1b[31m";
    }
    if (color === "green") {
        return "\x1b[32m";
    }
    if (color === "yellow") {
        return "\x1b[33m";
    }
    if (color === "blue") {
        return "\x1b[34m";
    }
    if (color === "magenta") {
        return "\x1b[35m";
    }
    throw Error(`unknown Color: ${color}`);
}
