import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { readRequestedFilesCache } from "../../parseDataset/cacheHandlers/cacheReader";
import { resolveInputBenchmarkingModelParams } from "../../parseDataset/core/itemsBuilder/buildBenchmarkingItems";
import { logBenchmarkingItems } from "../../parseDataset/utils/logBenchmarkingItems";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import { deserializeCodeElementRange } from "../../structures/common/codeElementPositions";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { LightweightBenchmarkingItem } from "../../structures/inputParameters/lightweight/lightweightBenchmarkingItem";
import { LightweightInputModelParams } from "../../structures/inputParameters/lightweight/lightweightInputModelParams";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import { ParsedCoqFileData } from "../../structures/parsedCoqFile/parsedCoqFileData";
import { makeStringsUnique } from "../../utils/collectionUtils/listUtils";
import {
    getOrThrow,
    groupBy,
    packIntoMap,
} from "../../utils/collectionUtils/mapUtils";
import { createParamsResolvers } from "../../utils/commonStructuresUtils/llmServicesUtils";
import { deserializeGoal } from "../../utils/coqUtils/goalParser";
import {
    getDatasetDir,
    joinPaths,
    listJsonFiles,
    readFile,
} from "../../utils/fileUtils/fs";

import { LightweightSerialization } from "./lightweightSerialization";

export namespace LightweightDeserializer {
    export function readSerializationFromDirectory(
        inputDirPath: string,
        logger: BenchmarkingLogger
    ): LightweightSerialization.PackedItems {
        const projects = readItemsFromJsonFiles<LightweightWorkspaceRoot>(
            inputDirPath,
            "projects"
        );
        const models = readItemsFromJsonFiles<LightweightInputModelParams>(
            inputDirPath,
            "models"
        );
        const items = readItemsFromJsonFiles<LightweightBenchmarkingItem>(
            inputDirPath,
            "items"
        );

        logger.info(
            `Lightweight serialization has been successfully read from "${inputDirPath}" directory`
        );

        return {
            projects: projects,
            models: models,
            items: items,
        };
    }

    function readItemsFromJsonFiles<T>(
        rootDirPath: string,
        itemsDirName: string
    ): T[] {
        const jsonFiles = listJsonFiles(
            joinPaths(rootDirPath, itemsDirName),
            1
        );
        const parsedItems = jsonFiles.map((filePath) => {
            const jsonString = readFile(filePath, (err) => {
                throw Error(
                    `Lightweight items parsing failed: failed to read ${filePath} file, ${err.message}`
                );
            });
            // TODO: validate with JSON schema
            return JSON.parse(jsonString) as T;
        });
        return parsedItems;
    }

    export function restoreBenchmarkingItems(
        serialization: LightweightSerialization.PackedItems,
        datasetCacheDirectoryPath: string,
        logger: BenchmarkingLogger
    ): BenchmarkingItem[] {
        const [workspaceRootsByRelativePaths, resolvedParamsByIds] =
            prepareResolutionMaps(serialization);

        const benchmarkingItems: BenchmarkingItem[] = [];
        const itemsByWorkspaces = groupBy(
            serialization.items,
            (item) => item.task.relativeWorkspacePath
        );
        for (const [
            relativeWorkspacePath,
            workspaceItems,
        ] of itemsByWorkspaces.entries()) {
            const workspaceRoot: WorkspaceRoot = getOrThrow(
                workspaceRootsByRelativePaths,
                relativeWorkspacePath,
                `Lightweight deserialization failed, invariant has been violated: no workspace root with "${relativeWorkspacePath}" relative path`
            );
            const restoredParsedCoqFiles = retrieveSourceFilesOfItems(
                workspaceItems.map((item) =>
                    joinPaths(
                        workspaceRoot.directoryPath,
                        item.task.relativeSourceFilePath
                    )
                ),
                workspaceRoot,
                datasetCacheDirectoryPath,
                logger
            );

            for (const item of workspaceItems) {
                const sourceFilePath = joinPaths(
                    workspaceRoot.directoryPath,
                    item.task.relativeSourceFilePath
                );
                benchmarkingItems.push(
                    ...restoreFromLightweightItem(
                        item,
                        workspaceRoot,
                        getOrThrow(
                            restoredParsedCoqFiles,
                            sourceFilePath,
                            `Lightweight deserialization failed, invariant has been violated: no \`ParsedCoqFileData\` for the requested "${sourceFilePath}" file`
                        ),
                        resolvedParamsByIds
                    )
                );
            }
        }

        logger
            .asOneRecord()
            .info(
                `Successfully constructed ${benchmarkingItems.length} benchmarking item(s) from lightweight one(s)`,
                undefined,
                ""
            )
            .debug(
                `:\n${logBenchmarkingItems(benchmarkingItems)}`,
                undefined,
                ""
            )
            .info("");

        return benchmarkingItems;
    }

    function prepareResolutionMaps(
        serialization: LightweightSerialization.PackedItems
    ): [
        Map<string, WorkspaceRoot>,
        Map<string, BenchmarkingModelParams<ModelParams>>,
    ] {
        const workspaceRootsByRelativePaths = packIntoMap(
            serialization.projects,
            (project) => project.relativeDirectoryPath,
            (project) => {
                return {
                    directoryPath: joinPaths(
                        getDatasetDir(),
                        project.relativeDirectoryPath
                    ),
                    requiresNixEnvironment: project.requiresNixEnvironment,
                } as WorkspaceRoot;
            }
        );
        const paramsResolvers = createParamsResolvers();
        const resolvedParamsByIds = packIntoMap(
            serialization.models,
            (params) => params.modelId,
            (params) => {
                const { llmServiceIdentifier, ...inputModelParams } = params;
                return resolveInputBenchmarkingModelParams(
                    inputModelParams,
                    params.llmServiceIdentifier,
                    paramsResolvers
                );
            }
        );
        return [workspaceRootsByRelativePaths, resolvedParamsByIds];
    }

    function retrieveSourceFilesOfItems(
        sourceFilePaths: string[],
        workspaceRoot: WorkspaceRoot,
        datasetCacheDirectoryPath: string,
        logger: BenchmarkingLogger
    ): Map<string, ParsedCoqFileData> {
        const uniqueSourceFilePaths = makeStringsUnique(sourceFilePaths);
        const workspaceCache = readRequestedFilesCache(
            uniqueSourceFilePaths,
            workspaceRoot.directoryPath,
            datasetCacheDirectoryPath,
            logger
        );
        const restoredParsedCoqFiles = packIntoMap(
            uniqueSourceFilePaths,
            (filePath) => filePath,
            (filePath) => {
                const cachedFile = workspaceCache.getCachedFile(filePath);
                if (cachedFile === undefined) {
                    // TODO: parse file if it is missing in cache
                    throw Error(
                        [
                            `Lightweight deserialization failed: file "${filePath}" is requested, `,
                            `but is not present in cache under "${datasetCacheDirectoryPath}" directory`,
                        ].join("")
                    );
                }
                return cachedFile.restoreParsedCoqFileData();
            }
        );
        return restoredParsedCoqFiles;
    }

    function restoreFromLightweightItem(
        item: LightweightBenchmarkingItem,
        workspaceRoot: WorkspaceRoot,
        parsedSourceFile: ParsedCoqFileData,
        resolvedParamsByIds: Map<string, BenchmarkingModelParams<ModelParams>>
    ): BenchmarkingItem[] {
        const task = item.task;
        const completionGenerationTask = new CompletionGenerationTask(
            deserializeGoal(task.goalToProve),
            deserializeCodeElementRange(task.positionRange),
            task.targetType,
            parsedSourceFile,
            getOrThrow(
                parsedSourceFile.theoremsByNames,
                task.sourceTheoremName,
                `Lightweight deserialization failed, invariant has been violated: no theorem object with the name "${task.sourceTheoremName}"`
            ),
            workspaceRoot
        );
        return item.targetModelIds.map((modelId) => {
            return {
                task: completionGenerationTask,
                params: getOrThrow(
                    resolvedParamsByIds,
                    modelId,
                    `Lightweight deserialization failed, invariant has been violated: no resolved model with "${modelId}" model id`
                ),
            };
        });
    }
}
