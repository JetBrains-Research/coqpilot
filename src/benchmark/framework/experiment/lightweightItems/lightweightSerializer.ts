import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { toFormattedJsonString } from "../../../../utils/printers";
import { throwError } from "../../../../utils/throwErrors";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import { serializeCodeElementRange } from "../../structures/common/codeElementPositions";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { InputBenchmarkingBundle } from "../../structures/inputParameters/inputBenchmarkingBundle";
import { InputBenchmarkingModelParams } from "../../structures/inputParameters/inputBenchmarkingModelParams";
import { LightweightBenchmarkingItem } from "../../structures/inputParameters/lightweight/lightweightBenchmarkingItem";
import { LightweightCompletionGenerationTask } from "../../structures/inputParameters/lightweight/lightweightCompletionGenerationTask";
import { LightweightInputModelParams } from "../../structures/inputParameters/lightweight/lightweightInputModelParams";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import { makeElementsUniqueByStringKeys } from "../../utils/collectionUtils/listUtils";
import {
    getOrThrow,
    groupByToEqualityMap,
    packIntoMap,
    reduceToMap,
} from "../../utils/collectionUtils/mapUtils";
import { serializeGoal } from "../../utils/coqUtils/goalParser";
import { buildSafeJsonFileName } from "../../utils/fileUtils/fileNameUtils";
import {
    clearDirectory,
    createDirectory,
    getDatasetDir,
    getLastName,
    joinPaths,
    relativizeAbsolutePaths,
    writeToFile,
} from "../../utils/fileUtils/fs";
import { prependWithZeros } from "../../utils/serializationUtils";

import { LightweightSerialization } from "./lightweightSerialization";

export namespace LightweightSerializer {
    export function serializeToLightweight(
        benchmarkingItems: BenchmarkingItem[],
        inputBundles: InputBenchmarkingBundle[]
    ): LightweightSerialization.PackedItems {
        const inputModels = inputBundles.flatMap(
            (bundle) => bundle.inputBenchmarkingModelsParams
        );
        const inputModelsByIds = packIntoMap(
            inputModels,
            (params) => params.modelId,
            (params) => params
        );

        const selectedProjects = makeElementsUniqueByStringKeys(
            benchmarkingItems.map((item) =>
                buildLightweightWorkspaceRoot(item.task.workspaceRoot)
            ),
            (workspaceRoot) => workspaceRoot.relativeDirectoryPath
        );
        const selectedLightweightModelsByIds = reduceToMap<
            BenchmarkingModelParams<ModelParams>,
            string,
            LightweightInputModelParams
        >(
            benchmarkingItems.map((item) => item.params),
            (params) => params.modelParams.modelId,
            (params) => {
                return {
                    ...(getOrThrow(
                        inputModelsByIds,
                        params.modelParams.modelId,
                        `Lightweight serialization failed, invariant has been violated: no input model with "${params.modelParams.modelId}" model id`
                    ) as InputBenchmarkingModelParams.Params),
                    llmServiceIdentifier: params.llmServiceIdentifier,
                };
            }
        );

        const lightweightItems = groupByToEqualityMap(
            benchmarkingItems,
            (item) => item.task,
            (item) => item.params.modelParams.modelId
        )
            .entries()
            .map(({ key: task, value: targetModelIds }) => {
                return {
                    task: buildLightweightTask(task),
                    targetModelIds: targetModelIds, // are expected to be unique already
                } as LightweightBenchmarkingItem;
            });

        return {
            projects: selectedProjects,
            models: Array.from(selectedLightweightModelsByIds.values()),
            items: lightweightItems,
        };
    }

    export function buildLightweightWorkspaceRoot(
        workspaceRoot: WorkspaceRoot
    ): LightweightWorkspaceRoot {
        return {
            relativeDirectoryPath: relativizeAbsolutePaths(
                getDatasetDir(),
                workspaceRoot.directoryPath
            ),
            requiresNixEnvironment: workspaceRoot.requiresNixEnvironment,
        };
    }

    export function buildLightweightTask(
        task: CompletionGenerationTask
    ): LightweightCompletionGenerationTask {
        return {
            goalToProve: serializeGoal(task.targetGoalToProve),
            positionRange: serializeCodeElementRange(task.targetPositionRange),
            targetType: task.targetType,
            relativeSourceFilePath: relativizeAbsolutePaths(
                task.workspaceRoot.directoryPath,
                task.sourceFilePath
            ),
            sourceTheoremName: task.sourceTheorem.name,
            relativeWorkspacePath: relativizeAbsolutePaths(
                getDatasetDir(),
                task.workspaceRoot.directoryPath
            ),
        };
    }

    export function saveSerializationToDirectory(
        serialization: LightweightSerialization.PackedItems,
        outputDirPath: string,
        logger: BenchmarkingLogger
    ) {
        clearDirectory(outputDirPath); // TODO: clear directory optionally

        saveAsJsonFiles(
            serialization.projects,
            outputDirPath,
            "projects",
            (project, _) =>
                buildSafeJsonFileName(
                    getLastName(project.relativeDirectoryPath)
                )
        );
        saveAsJsonFiles(
            serialization.models,
            outputDirPath,
            "models",
            (inputModel, _) => buildSafeJsonFileName(inputModel.modelId)
        );
        saveAsJsonFiles(
            serialization.items,
            outputDirPath,
            "items",
            (item, itemIndex) =>
                buildUniqueItemFileName(
                    item,
                    itemIndex,
                    serialization.items.length - 1
                )
        );

        logger.info(
            `Lightweight serialization has been successfully saved into "${outputDirPath}" directory`
        );
    }

    function buildUniqueItemFileName(
        item: LightweightBenchmarkingItem,
        itemIndex: number,
        maxIndex: number
    ): string {
        const augmentedIndex = prependWithZeros(itemIndex, maxIndex);
        const fileIdentifier = item.task.relativeSourceFilePath;
        const unsafeFileName = `${augmentedIndex}-${fileIdentifier}-${item.task.sourceTheoremName}`;
        return buildSafeJsonFileName(unsafeFileName);
    }

    function saveAsJsonFiles<T>(
        items: T[],
        rootDirPath: string,
        itemsDirName: string,
        buildItemFileName: (item: T, itemIndex: number) => string
    ) {
        const itemsDirPath = createDirectory(true, rootDirPath, itemsDirName);
        for (let i = 0; i < items.length; i++) {
            const item = items[i];
            const itemFilePath = joinPaths(
                itemsDirPath,
                buildItemFileName(item, i)
            );
            writeToFile(toFormattedJsonString(item), itemFilePath, (err) =>
                throwError(
                    "Lightweight serialization failed: ",
                    `failed to save ${itemFilePath} file, ${err.message}`
                )
            );
        }
    }
}
