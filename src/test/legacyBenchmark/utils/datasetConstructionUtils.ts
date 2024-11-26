import * as fs from "fs";

export class DatasetItem {
    workspaceRootPath: string | undefined;
    specificTheoremsForBenchmark: string[] | undefined;

    /* Paths should be relative to 'dataset' folder */
    constructor(
        public path: string,
        specificTheoremsForBenchmark: string[] | undefined = undefined,
        workspaceRootPath: string | undefined = undefined
    ) {
        this.workspaceRootPath = workspaceRootPath;
        this.specificTheoremsForBenchmark = specificTheoremsForBenchmark;
    }
}

export function datasetFromJson(
    filePath: string,
    projectRootPath: string
): DatasetItem[] {
    const datasetJson = JSON.parse(
        fs.readFileSync(filePath, "utf-8")
    ) as Record<string, string[]>;

    let dataset: DatasetItem[] = [];
    for (const [theoremFilePath, theorems] of Object.entries(datasetJson)) {
        dataset.push(
            new DatasetItem(theoremFilePath, theorems, projectRootPath)
        );
    }

    return dataset;
}
