import { BenchmarkedItem } from "../../structures/benchmarkingResults/benchmarkedItem";
import { AbstractReport } from "../abstractReport";

export namespace ModelsToAggregatedGroupsTable {
    export interface Options {}

    export class Report extends AbstractReport<{}, {}> {
        constructor(
            benchmarkedItems: BenchmarkedItem[],
            inputOptions: Partial<Options>
        ) {
            super();
        }

        protected toMarkdownString(options: {}): string {
            throw new Error("Method not implemented.");
        }
        protected toLatexString(options: {}): string {
            throw new Error("Method not implemented.");
        }
        protected resolveMarkdownOptions(inputOptions: Partial<{}>): {} {
            throw new Error("Method not implemented.");
        }
        protected resolveLatexOptions(inputOptions: Partial<{}>): {} {
            throw new Error("Method not implemented.");
        }
    }
}
