import { sort } from "../../../../utils/collectionUtils/listUtils";
import { unreachable } from "../../../../utils/errors/throwErrors";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import { BenchmarkedItem } from "../../structures/benchmarkingResults/benchmarkedItem";
import { AbstractReport } from "../utils/abstractReport";
import { LatexUtils } from "../utils/latexUtils";
import { MarkdownUtils } from "../utils/markdownUtils";
import { mapTableRow } from "../utils/tableUtils";

import { ModelsToAggregatedGroupsImpl } from "./implementation";

// TODO: support other values aggregation, such as, for example, unique theorems proven
export namespace ModelsToAggregatedGroups {
    export interface AggregatedRow {
        name: string;
        shouldAggregateModel: (params: BenchmarkingModelParams) => boolean;
    }

    export interface Options {
        /**
         * Returns the name of the model to show in the first column
         * of the table being built. If `undefined` is returned,
         * the corresponding model will be excluded from the table.
         *
         * By default, this mapper uses the given `modelId`
         * as the name of the model to show.
         */
        modelsMapper: (params: BenchmarkingModelParams) => string | undefined;

        /**
         * Returns the names of the groups to aggregate the given `task` to.
         * This names will be shown in the first row of the table.
         * If empty list is returned, the corresponding task will be excluded
         * from the aggregation.
         *
         * `groupReadFromFile` parameter provides access to the group determined
         * by the `theoremsByGroupsFiles` option.
         *
         * Default `groupsMapper` returns `groupReadFromFile` if present or [] for any task,
         * effectively enabling only such groups specified through `theoremsByGroupsFiles`.
         */
        groupsMapper: (
            task: CompletionGenerationTask,
            groupReadFromFile: string | undefined
        ) => string[];

        /**
         * To ease the groups mapping, files with already grouped theorems can be used.
         *
         * Each file should describe one group. The file should include
         * `SerializedGroup` structure serialized as JSON.
         *
         * The order of resolving the group of the task is the following:
         * first, the value is optionally defined by `theoremsByGroupsFiles`;
         * then, `groupsMapper` is used, so as to resolve the unclassified task
         * or to override the group assigned by the files data.
         *
         * By default, no groups mapping files are used.
         */
        theoremsByGroupsFiles: string[];

        /**
         * Specifies the way to show the value of the cell with the aggregated completions number.
         *
         * By default, it shows percentage with the precision of two significant digits.
         */
        showAggregatedCell: (
            successfulCompletionsInGroup: number,
            totalCompletionsInGroup: number
        ) => string;

        /**
         * Extra rows aggregating specific models.
         *
         * By default, no extra rows are added.
         */
        extraAggregatedRows: AggregatedRow[];

        /**
         * Enables "All methods together" row, which aggregates all the models together.
         * Is enabled by default.
         */
        enableAllMethodsTogetherRow: boolean;

        /**
         * Enables "Total" column, which aggregates theorems of all the groups together.
         * If no groups are present, aggregates all available theorems.
         * Is enabled by default.
         */
        enableTotalColumn: boolean;

        /**
         * Specify order of columns: `groups` represents columns of groups,
         * `totalColumn` corresponds to the "Total" column (if enabled).
         *
         * This method should return a valid permutation of the columns;
         * otherwise, an error will be thrown.
         *
         * By default, groups are sorted as strings and then are followed by `totalColumn`.
         */
        sortColumns: (
            groups: string[],
            totalColumn: string | undefined
        ) => string[];

        /**
         * Specify order of rows: `models` represents rows of models,
         * `addedRows` corresponds to rows added via `extraAggregatedRows` option,
         * and `allMethodsTogetherRow` to the "All methods together" one (if enabled).
         *
         * This method should return a valid permutation of the rows;
         * otherwise, an error will be thrown.
         *
         * By default, each block is sorted as strings and the general order is:
         * `models`, then `addedRows`, then `allMethodsTogetherRow`.
         */
        sortRows: (
            models: string[],
            addedRows: string[],
            allMethodsTogetherRow: string | undefined
        ) => string[];
    }

    function resolveOptions(inputOptions: Partial<Options>): Options {
        return {
            modelsMapper:
                inputOptions.modelsMapper ??
                ((params: BenchmarkingModelParams) =>
                    params.modelParams.modelId),

            groupsMapper:
                inputOptions.groupsMapper ??
                ((
                    _: CompletionGenerationTask,
                    groupReadFromFile: string | undefined
                ) => {
                    return groupReadFromFile === undefined
                        ? []
                        : [groupReadFromFile];
                }),
            theoremsByGroupsFiles: inputOptions.theoremsByGroupsFiles ?? [],

            showAggregatedCell:
                inputOptions.showAggregatedCell ??
                ((
                    theoremsProvedInGroup: number,
                    totalTheoremsInGroup: number
                ) => {
                    const percentage =
                        (theoremsProvedInGroup / totalTheoremsInGroup) * 100;
                    return `${+percentage.toPrecision(2)}%`;
                }),

            extraAggregatedRows: inputOptions.extraAggregatedRows ?? [],

            enableAllMethodsTogetherRow:
                inputOptions.enableAllMethodsTogetherRow ?? true,
            enableTotalColumn: inputOptions.enableTotalColumn ?? true,

            sortColumns:
                inputOptions.sortColumns ??
                ((groups: string[], totalColumn: string | undefined) => {
                    const sorted = sort(groups);
                    if (totalColumn !== undefined) {
                        sorted.push(totalColumn);
                    }
                    return sorted;
                }),
            sortRows:
                inputOptions.sortRows ??
                ((
                    models: string[],
                    addedRows: string[],
                    allMethodsTogetherRow: string | undefined
                ) => {
                    const sorted = [...sort(models), ...sort(addedRows)];
                    if (allMethodsTogetherRow !== undefined) {
                        sorted.push(allMethodsTogetherRow);
                    }
                    return sorted;
                }),
        };
    }

    // TODO: more customization can be supported via format-specific options
    export interface MarkdownOptions {
        rowsToMakeBold: string[];
    }

    export interface LatexOptions {
        enableBoldColumnsTitles: boolean;
        rowsToMakeBold: string[];
        addMidRulesAfterRows: number[];
    }

    export class Report extends AbstractReport<MarkdownOptions, LatexOptions> {
        private readonly reportOptions: Options;

        constructor(
            private readonly benchmarkedItems: BenchmarkedItem[],
            inputOptions: Partial<Options>
        ) {
            super();
            this.reportOptions = resolveOptions(inputOptions);
        }

        protected resolveMarkdownOptions(
            inputOptions: Partial<MarkdownOptions>
        ): MarkdownOptions {
            return {
                rowsToMakeBold: inputOptions.rowsToMakeBold ?? [
                    ModelsToAggregatedGroupsImpl.ALL_METHODS_TOGETHER_ROW_TITLE,
                ],
            };
        }

        protected toMarkdownString(options: MarkdownOptions): string {
            const abstractTable =
                ModelsToAggregatedGroupsImpl.buildAggregatedTable(
                    this.benchmarkedItems,
                    this.reportOptions
                );
            const formattedTable = abstractTable.toString2DListEquallyFormatted(
                (value) => value
            );
            if (formattedTable.length === 0) {
                unreachable("built table always has columns titles row");
            }

            options.rowsToMakeBold.forEach((rowTitle) =>
                mapTableRow(
                    formattedTable,
                    MarkdownUtils.makeBold,
                    undefined,
                    rowTitle
                )
            );

            const allMdTableLines = MarkdownUtils.asTableLines(formattedTable);
            return allMdTableLines.join("\n");
        }

        protected resolveLatexOptions(
            inputOptions: Partial<LatexOptions>
        ): LatexOptions {
            return {
                enableBoldColumnsTitles:
                    inputOptions.enableBoldColumnsTitles ?? true,
                rowsToMakeBold: inputOptions.rowsToMakeBold ?? [
                    ModelsToAggregatedGroupsImpl.ALL_METHODS_TOGETHER_ROW_TITLE,
                ],
                addMidRulesAfterRows: inputOptions.addMidRulesAfterRows ?? [],
            };
        }

        protected toLatexString(options: LatexOptions): string {
            const abstractTable =
                ModelsToAggregatedGroupsImpl.buildAggregatedTable(
                    this.benchmarkedItems,
                    this.reportOptions
                );
            const formattedTable = abstractTable.toString2DListEquallyFormatted(
                LatexUtils.escapeSpecialCharacters
            );
            if (formattedTable.length === 0) {
                unreachable("built table always has columns titles row");
            }

            if (options.enableBoldColumnsTitles) {
                mapTableRow(formattedTable, LatexUtils.makeBold, 0);
            }
            options.rowsToMakeBold.forEach((rowTitle) =>
                mapTableRow(
                    formattedTable,
                    LatexUtils.makeBold,
                    undefined,
                    rowTitle
                )
            );

            const latexTableLines = formattedTable.map(
                LatexUtils.joinAsTableLine
            );

            const midRulesIndexes = new Set(options.addMidRulesAfterRows);
            midRulesIndexes.add(0);

            const latexTableLinesWithMidRules: string[] = [];
            latexTableLines.forEach((line, lineIndex) => {
                latexTableLinesWithMidRules.push(line);
                if (midRulesIndexes.has(lineIndex)) {
                    latexTableLinesWithMidRules.push(LatexUtils.MID_RULE);
                }
            });

            const latexLines = LatexUtils.wrapIntoTableEnvironment(
                formattedTable[0].length - 1,
                [
                    LatexUtils.TOP_RULE,
                    ...latexTableLinesWithMidRules,
                    LatexUtils.BOTTOM_RULE,
                ]
            );
            return latexLines.join("\n");
        }
    }
}
