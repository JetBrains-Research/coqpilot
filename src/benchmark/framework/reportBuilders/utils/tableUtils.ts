export function mapTableRow(
    table: string[][],
    mapRowValues: (value: string) => string,
    rowIndex?: number,
    rowTitle?: string
) {
    const actualRawIndex =
        rowIndex ?? table.findIndex((row) => row[0] === rowTitle);
    if (actualRawIndex !== -1) {
        table[actualRawIndex] = table[actualRawIndex].map(mapRowValues);
    }
}
