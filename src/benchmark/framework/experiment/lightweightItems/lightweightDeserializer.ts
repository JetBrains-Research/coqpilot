import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { deserializeLLMService } from "../../../../llm/llmServices/utils/serialization/serializedLLMService";
import { LLMServicesStorage } from "../../../../llm/llmServicesStorage";

import { makeStringsUnique } from "../../../../utils/collectionUtils/listUtils";
import {
    getOrThrow,
    groupBy,
    packIntoMap,
} from "../../../../utils/collectionUtils/mapUtils";
import { throwError } from "../../../../utils/errors/throwErrors";
import { readFile } from "../../../../utils/fs/fileUtils";
import { listJsonFiles } from "../../../../utils/fs/listFiles";
import { joinPaths } from "../../../../utils/fs/pathUtils";
import { getDatasetDir } from "../../../../utils/fs/rootResolvers";
import { deserializeCodeElementRange } from "../../../../utils/structures/codeElementPositions";
import { BENCHMARKING_CONTROL_PARAMS } from "../../benchmarkingCore/executeBenchmarkingTask";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { readRequestedFilesCache } from "../../parseDataset/cacheHandlers/cacheReader";
import { resolveInputBenchmarkingModelParams } from "../../parseDataset/core/itemsBuilder/buildBenchmarkingItems";
import { logBenchmarkingItems } from "../../parseDataset/utils/logBenchmarkingItems";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { LightweightBenchmarkingItem } from "../../structures/inputParameters/lightweight/lightweightBenchmarkingItem";
import { LightweightInputModelParams } from "../../structures/inputParameters/lightweight/lightweightInputModelParams";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import { ParsedCoqFileData } from "../../structures/parsedCoqFile/parsedCoqFileData";
import { deserializeGoal } from "../../utils/coqUtils/goalParser";

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
            const jsonString = readFile(filePath, (err) =>
                throwError(
                    "Lightweight items parsing failed: ",
                    `failed to read ${filePath} file, ${err.message}`
                )
            );
            // TODO: validate with JSON schema
            return JSON.parse(jsonString) as T;
        });
        return parsedItems;
    }

    export function restoreBenchmarkingItems(
        serialization: LightweightSerialization.PackedItems,
        datasetCacheDirectoryPath: string,
        logger: BenchmarkingLogger
    ): [LLMServicesStorage, BenchmarkingItem[]] {
        const [
            workspaceRootsByRelativePaths,
            resolvedParamsByIds,
            llmServices,
        ] = prepareResolutionMaps(serialization, logger);
        try {
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

            return [llmServices, benchmarkingItems];
        } catch (e) {
            llmServices.dispose();
            throw e;
        }
    }

    function prepareResolutionMaps(
        serialization: LightweightSerialization.PackedItems,
        logger: BenchmarkingLogger
    ): [
        Map<string, WorkspaceRoot>,
        Map<string, BenchmarkingModelParams<ModelParams>>,
        LLMServicesStorage,
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
        const llmServices = new LLMServicesStorage();
        try {
            const resolvedParamsByIds = packIntoMap(
                serialization.models,
                (params) => params.modelId,
                (params) => {
                    const {
                        serializedService: serializedLLMService,
                        ...inputModelParams
                    } = params;
                    const serviceCtor =
                        deserializeLLMService(serializedLLMService);
                    const newService = llmServices.registerService(() =>
                        serviceCtor(BENCHMARKING_CONTROL_PARAMS)
                    );
                    return resolveInputBenchmarkingModelParams(
                        inputModelParams,
                        newService,
                        logger
                    );
                }
            );
            return [
                workspaceRootsByRelativePaths,
                resolvedParamsByIds,
                llmServices,
            ];
        } catch (e) {
            llmServices.dispose();
            throw e;
        }
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
                    throwError(
                        "Lightweight deserialization failed: ",
                        `file "${filePath}" is requested, but is not present in cache `,
                        `under "${datasetCacheDirectoryPath}" directory`
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
