import { joinList } from "../../../../utils/collectionUtils/listUtils";

export namespace LatexUtils {
    export const BACKSLASH = "\\";
    export const LINE_BREAK = `${BACKSLASH}${BACKSLASH}`;

    export const TOP_RULE = `${BACKSLASH}toprule`;
    export const MID_RULE = `${BACKSLASH}midrule`;
    export const BOTTOM_RULE = `${BACKSLASH}bottomrule`;

    export function makeBold(text: string): string {
        return `${BACKSLASH}textbf{${text}}`;
    }

    /**
     * Currently supports escaping only "{}_#$&%" symbols.
     */
    // TODO: support proper escaping of more symbols
    export function escapeSpecialCharacters(text: string): string {
        return text.replace(/([{}_#$&%])/g, `${BACKSLASH}$1`);
    }

    export function joinAsTableLine(row: string[]): string {
        return joinList(row, " & ", "", ` ${LINE_BREAK}`);
    }

    export function wrapIntoTableEnvironment(
        dataColumnsNumber: number,
        inputLines: string[]
    ): string[] {
        return [
            "\\begin{table}",
            "\\centering",
            `\\begin{tabular}{l${"c".repeat(dataColumnsNumber)}}`,
            ...inputLines,
            "\\end{tabular}",
            "\\end{table}",
        ];
    }
}
