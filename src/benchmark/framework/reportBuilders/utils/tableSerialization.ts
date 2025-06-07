import { invariantFailed } from "../../../../utils/errors/throwErrors";
import { stringifyAnyValue, stringifyList } from "../../../../utils/printers";

export namespace TableSerialization {
    export class Row<T> {
        constructor(
            readonly title: string,
            private readonly values: T[],
            readonly valuesLength: number
        ) {
            if (values.length !== valuesLength) {
                invariantFailed(
                    "`Row`",
                    `\`valuesLength\` is ${valuesLength}, but `,
                    `values are: ${stringifyList(values)}`
                );
            }
        }

        toStringList(
            valueToString: (value: T) => string = stringifyAnyValue,
            mapTitle: (title: string) => string = (title) => title
        ): string[] {
            return [mapTitle(this.title), ...this.values.map(valueToString)];
        }

        getValue(colIndex: number): T {
            this.validateColIndex(colIndex, `failed to get value`);
            return this.values[colIndex];
        }

        setValue(colIndex: number, newValue: T) {
            this.validateColIndex(
                colIndex,
                `failed to set new value ${stringifyAnyValue(newValue)}`
            );
            this.values[colIndex] = newValue;
        }

        private validateColIndex(colIndex: number, actionMessage: string) {
            if (colIndex < 0 || colIndex > this.values.length) {
                invariantFailed(
                    "`Row`",
                    actionMessage,
                    ` at column number ${colIndex} of row ${stringifyList(this.toStringList())}: `,
                    `${colIndex} is not in 0..${this.values.length}`
                );
            }
        }
    }

    // TODO: support styling cells
    // (each cell might have enum value with its style, e.g. BOLD, ITALIC, ...)
    export class Table<T> {
        private readonly dataColumnsLength: number;

        constructor(
            private readonly columnsTitlesRow: Row<string>,
            private readonly dataRows: Row<T>[]
        ) {
            this.dataColumnsLength = columnsTitlesRow.valuesLength;
            for (const row of dataRows) {
                this.validateRowLength(row);
            }
        }

        static fromColumnsNames<T>(
            firstRowTitle: string,
            columnsTitles: string[]
        ): Table<T> {
            const columnsTitlesRows = new Row<string>(
                firstRowTitle,
                columnsTitles,
                columnsTitles.length
            );
            return new Table<T>(columnsTitlesRows, []);
        }

        addDataRow(rowTitle: string, rowValues: T[]) {
            const newRow = new Row<T>(rowTitle, rowValues, rowValues.length);
            this.validateRowLength(newRow);
            this.dataRows.push(newRow);
        }

        toString2DList(
            mapDataValues: (value: T) => string = stringifyAnyValue,
            mapColumnsNames: (columnName: string) => string = (columnName) =>
                columnName,
            mapRowsTitles: (rowTitle: string) => string = (rowTitle) => rowTitle
        ): string[][] {
            return [
                this.columnsTitlesRow.toStringList(
                    mapColumnsNames,
                    mapRowsTitles
                ),
                ...this.dataRows.map((dataRow) =>
                    dataRow.toStringList(mapDataValues, mapRowsTitles)
                ),
            ];
        }

        toString2DListEquallyFormatted(
            mapStringValue: (value: string) => string
        ): string[][] {
            return this.toString2DList(
                (dataValue) => mapStringValue(dataValue as string),
                mapStringValue,
                mapStringValue
            );
        }

        private validateRowLength(row: Row<T>) {
            if (row.valuesLength !== this.dataColumnsLength) {
                invariantFailed(
                    "`Table`",
                    `\`valueColsLength\` is ${this.dataColumnsLength}, but `,
                    `input data row has ${row.valuesLength} values: ${stringifyList(row.toStringList())}]`
                );
            }
        }
    }
}
