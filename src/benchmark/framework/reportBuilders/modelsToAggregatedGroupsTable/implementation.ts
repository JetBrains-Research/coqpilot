import { EqualitySet } from "../../../../utils/collectionUtils/equalitySet";
import {
    isPermutation,
    makeElementsUnique,
} from "../../../../utils/collectionUtils/listUtils";
import {
    getOrPut,
    mapValues,
} from "../../../../utils/collectionUtils/mapUtils";
import {
    illegalState,
    unreachable,
} from "../../../../utils/errors/throwErrors";
import { stringifyList } from "../../../../utils/printers";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import { BenchmarkedItem } from "../../structures/benchmarkingResults/benchmarkedItem";
import { reportBuilderFailed } from "../utils/errors";
import { TableSerialization } from "../utils/tableSerialization";

import { ModelsToAggregatedGroups } from "./report";

export namespace ModelsToAggregatedGroupsImpl {
    type Options = ModelsToAggregatedGroups.Options;
    type AggregatedRow = ModelsToAggregatedGroups.AggregatedRow;

    import Structs = TableSerialization;
    export type AggregatedTable = Structs.Table<string>;

    export const CORNER_TITLE = "Methods / Groups";
    export const TOTAL_COLUMN_NAME = "Total";
    export const ALL_METHODS_TOGETHER_ROW_TITLE = "All methods together";

    export function buildAggregatedTable(
        items: BenchmarkedItem[],
        options: Options
    ): AggregatedTable {
        const columnToItems = groupItemsByColumns(items, options);
        const sortedColumns = prepareColumnsTitles(columnToItems, options);
        if (sortedColumns.length === 1) {
            /**
             * If no groups are present, "Total" should
             * aggregate all items.
             */
            columnToItems.set(TOTAL_COLUMN_NAME, items);
        }
        const columnsTotalValues = calculateColumnsTotalValues(
            columnToItems,
            sortedColumns
        );

        const rowsToAdd = prepareRowsToAdd(options);
        const rowTitleToValues = buildRows(
            columnToItems,
            sortedColumns,
            rowsToAdd,
            options
        );
        const sortedRows = prepareRowsTitles(
            rowTitleToValues,
            rowsToAdd,
            options
        );

        return constructTable(
            sortedColumns,
            sortedRows,
            rowTitleToValues,
            columnsTotalValues,
            options
        );
    }

    function groupItemsByColumns(
        items: BenchmarkedItem[],
        options: Options
    ): Map<string, BenchmarkedItem[]> {
        const columnToItems = new Map<string, BenchmarkedItem[]>();
        // TODO (!): support reading groups from files
        for (const item of items) {
            const itemGroups = options.groupsMapper(item.item.task, undefined);
            if (options.enableTotalColumn && itemGroups.length !== 0) {
                /**
                 * Since "Total" column should aggregate the total
                 * among the actual groups (if present), the item
                 * with the task excluded from all groups should be excluded
                 * from the "Total" too.
                 */
                itemGroups.push(TOTAL_COLUMN_NAME);
            }
            for (const itemGroup of itemGroups) {
                const groupItems = getOrPut(
                    columnToItems,
                    itemGroup,
                    () => [] as BenchmarkedItem[]
                );
                groupItems.push(item);
            }
        }
        return columnToItems;
    }

    function prepareColumnsTitles(
        columnToItems: Map<string, BenchmarkedItem[]>,
        options: Options
    ): string[] {
        const actualGroups = Array.from(columnToItems.keys()).filter(
            (groupName) => groupName !== TOTAL_COLUMN_NAME
        );
        const actualColumns = options.enableTotalColumn
            ? [...actualGroups, TOTAL_COLUMN_NAME]
            : actualGroups;
        const sortedColumns = options.sortColumns(
            actualGroups,
            options.enableTotalColumn ? TOTAL_COLUMN_NAME : undefined
        );
        if (!isPermutation(actualColumns, sortedColumns)) {
            reportBuilderFailed(
                "`sortColumns` did not produce a correct permutation: ",
                `actual columns ${stringifyList(actualColumns)}, `,
                `sorted columns ${stringifyList(sortedColumns)}`
            );
        }
        return sortedColumns;
    }

    function calculateColumnsTotalValues(
        columnToItems: Map<string, BenchmarkedItem[]>,
        sortedColumns: string[]
    ): number[] {
        const columnsTotalValues = mapValues(
            columnToItems,
            (_: string, items: BenchmarkedItem[]) =>
                makeElementsUnique(items.map((item) => item.item.task)).length
        );
        return sortedColumns.map(
            (columnTitle) =>
                columnsTotalValues.get(columnTitle) ??
                illegalState(`unexpected column title "${columnTitle}"`)
        );
    }

    function prepareRowsToAdd(options: Options): AggregatedRow[] {
        const rowsToAdd: AggregatedRow[] = [...options.extraAggregatedRows];
        if (options.enableAllMethodsTogetherRow) {
            rowsToAdd.push({
                name: ALL_METHODS_TOGETHER_ROW_TITLE,
                shouldAggregateModel: (params) =>
                    options.modelsMapper(params) !== undefined,
            });
        }
        return rowsToAdd;
    }

    function buildTasksTrackingRow(
        columnsNumber: number
    ): EqualitySet<CompletionGenerationTask>[] {
        const row = [];
        for (let i = 0; i < columnsNumber; i++) {
            row.push(new EqualitySet<CompletionGenerationTask>());
        }
        return row;
    }

    function buildRows(
        columnToItems: Map<string, BenchmarkedItem[]>,
        sortedColumns: string[],
        rowsToAdd: AggregatedRow[],
        options: Options
    ): Map<string, number[]> {
        const columnsNumber = sortedColumns.length;
        const columnTitleToIndex = new Map<string, number>();
        sortedColumns.forEach((columnTitle, index) =>
            columnTitleToIndex.set(columnTitle, index)
        );

        /**
         * Note: `rowToAdd` might containt aggregation of several models;
         * that requires calculating **only unique** successful completions explicitly.
         */
        const rowsToAddOkTasksByColumns: [
            AggregatedRow,
            EqualitySet<CompletionGenerationTask>[],
        ][] = rowsToAdd.map((rowToAdd) => [
            rowToAdd,
            buildTasksTrackingRow(columnsNumber),
        ]);

        const rowTitleToValues = new Map<string, number[]>();
        for (const [columnTitle, items] of columnToItems.entries()) {
            const columnIndex =
                columnTitleToIndex.get(columnTitle) ??
                unreachable(
                    `unexpected column title "${columnTitle}" after passed permutation check`
                );
            for (const item of items) {
                const isOkTask = item.result.isSuccessfulCompletion();

                for (const [
                    rowToAdd,
                    tasksByColumns,
                ] of rowsToAddOkTasksByColumns) {
                    if (!rowToAdd.shouldAggregateModel(item.item.params)) {
                        continue;
                    }
                    if (isOkTask) {
                        tasksByColumns[columnIndex].add(item.item.task);
                    }
                }

                const model = options.modelsMapper(item.item.params);
                if (model === undefined) {
                    continue;
                }
                const modelRow = getOrPut(rowTitleToValues, model, () =>
                    Array(columnsNumber).fill(0)
                );
                modelRow[columnIndex] += isOkTask ? 1 : 0;
            }
        }

        for (const [rowToAdd, tasksByColumns] of rowsToAddOkTasksByColumns) {
            rowTitleToValues.set(
                rowToAdd.name,
                tasksByColumns.map((columnOkTasks) => columnOkTasks.size())
            );
        }

        return rowTitleToValues;
    }

    function prepareRowsTitles(
        rowTitleToValues: Map<string, number[]>,
        rowsToAdd: AggregatedRow[],
        options: Options
    ) {
        const extraRowsToAddNames = options.extraAggregatedRows.map(
            (row) => row.name
        );
        const rowsToAddNames = new Set(rowsToAdd.map((row) => row.name));
        const actualRows = Array.from(rowTitleToValues.keys());
        const actualModels = actualRows.filter(
            (title) => !rowsToAddNames.has(title)
        );
        const sortedRows = options.sortRows(
            actualModels,
            extraRowsToAddNames,
            options.enableAllMethodsTogetherRow
                ? ALL_METHODS_TOGETHER_ROW_TITLE
                : undefined
        );
        if (!isPermutation(actualRows, sortedRows)) {
            reportBuilderFailed(
                "`sortRows` did not produce a correct permutation: ",
                `actual rows ${stringifyList(actualRows)}, `,
                `sorted rows ${stringifyList(sortedRows)}`
            );
        }
        return sortedRows;
    }

    function constructTable(
        sortedColumns: string[],
        sortedRows: string[],
        rowTitleToValues: Map<string, number[]>,
        columnsTotalValues: number[],
        options: Options
    ) {
        const table = Structs.Table.fromColumnsNames<string>(
            CORNER_TITLE,
            sortedColumns
        );
        for (const rowTitle of sortedRows) {
            const rowValuesByColumns =
                rowTitleToValues.get(rowTitle) ??
                unreachable(
                    `unexpected row title "${rowTitle}" after passed permutation check`
                );
            const rowResultsByColumns = rowValuesByColumns.map(
                (successfulCompletionsNumber, columndIndex) =>
                    options.showAggregatedCell(
                        successfulCompletionsNumber,
                        columnsTotalValues[columndIndex]
                    )
            );
            table.addDataRow(rowTitle, rowResultsByColumns);
        }

        return table;
    }
}
