import { joinListWrapped } from "../../../../utils/collectionUtils/listUtils";

export namespace MarkdownUtils {
    export const TABLE_SEPARATOR = "|";
    export const TABLE_WIDTH_SYMBOL = "-";

    export function makeBold(text: string): string {
        return `**${text}**`;
    }

    export function buildTableWidthLine(columnsTitlesRow: string[]): string {
        return joinListWrapped(
            columnsTitlesRow.map((title) =>
                TABLE_WIDTH_SYMBOL.repeat(title.length)
            ),
            TABLE_SEPARATOR
        );
    }

    export function joinAsTableLine(row: string[]): string {
        return joinListWrapped(
            row.map((value) => ` ${value} `),
            TABLE_SEPARATOR
        );
    }

    export function asTableLines(formattedTable: string[][]): string[] {
        const mdTableWidthLine = MarkdownUtils.buildTableWidthLine(
            formattedTable[0]
        );
        const mdTableLines = formattedTable.map(MarkdownUtils.joinAsTableLine);
        const allMdTableLines = [
            mdTableLines[0],
            mdTableWidthLine,
            ...mdTableLines.slice(1),
        ];
        return allMdTableLines;
    }
}
