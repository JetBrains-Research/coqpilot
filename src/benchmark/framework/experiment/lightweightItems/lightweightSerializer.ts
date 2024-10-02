import { toJsonString } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import {
    deserializeCodeElementRange,
    serializeCodeElementRange,
} from "../../structures/common/codeElementPositions";
import { WorkspaceRoot } from "../../structures/common/workspaceRoot";
import { InputBenchmarkingBundle } from "../../structures/inputParameters/inputBenchmarkingBundle";
import { InputBenchmarkingModelParams } from "../../structures/inputParameters/inputBenchmarkingModelParams";
import { LightweightBenchmarkingItem } from "../../structures/inputParameters/lightweight/lightweightBenchmarkingItem";
import { LightweightCompletionGenerationTask } from "../../structures/inputParameters/lightweight/lightweightCompletionGenerationTask";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import { makeElementsUniqueByStringKeys } from "../../utils/collectionUtils/listUtils";
import {
    getOrThrow,
    groupByToEqualityMap,
    packIntoMap,
    reduceToMap,
} from "../../utils/collectionUtils/mapUtils";
import {
    deserializeGoal,
    goalToProveAsString,
    serializeGoal,
} from "../../utils/coqUtils/goalParser";
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
import { getTargetTypeName } from "../../utils/serializationUtils";

export namespace LightweightSerializer {
    export interface LightweightSerialization {
        projects: LightweightWorkspaceRoot[];
        models: InputBenchmarkingModelParams.Params[];
        items: LightweightBenchmarkingItem[];
    }

    export function serializeToLightweight(
        benchmarkingItems: BenchmarkingItem[],
        inputBundles: InputBenchmarkingBundle[]
    ): LightweightSerialization {
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
        const selectedInputModelsByIds = reduceToMap<
            string,
            string,
            InputBenchmarkingModelParams.Params
        >(
            benchmarkingItems.map((item) => item.params.modelParams.modelId),
            (modelId) => modelId,
            (modelId) =>
                getOrThrow(
                    inputModelsByIds,
                    modelId,
                    `Lightweight serialization failed, invariant has been violated: no input model with "${modelId}" model id`
                )
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
            models: Array.from(selectedInputModelsByIds.values()),
            items: lightweightItems,
        };
    }

    function buildLightweightWorkspaceRoot(
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

    function buildLightweightTask(
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

    export function logSerialization(
        serialization: LightweightSerialization,
        logger: BenchmarkingLogger
    ) {
        logger
            .asOneRecord()
            .info("Successfully prepared lightweight serialization:")
            .info(`- ${serialization.projects.length} project(s)`)
            .debug(
                `${serialization.projects.map((project) => `  * "${project.relativeDirectoryPath}"`).join("\n")}\n`
            )
            .info(`- ${serialization.models.length} model(s)`)
            .debug(
                `${serialization.models.map((model) => `  * "${model.modelId}"`).join("\n")}\n`
            )
            .info(`- ${serialization.items.length} item(s)`)
            .debug(
                `${serialization.items.map((item, index) => `  * Lightweight benchmarking item ${index}:\n${logLightweightItem(item, "    ")}`).join("\n  ---\n")}`
            );
    }

    function logLightweightItem(
        item: LightweightBenchmarkingItem,
        indent: string
    ): string {
        const task = item.task;
        const targetLog = `> target: ${getTargetTypeName(task.targetType)}, goal \`${goalToProveAsString(deserializeGoal(task.goalToProve))}\``;
        const sourceLog = `> source: ${deserializeCodeElementRange(task.positionRange)} of theorem "${task.sourceTheoremName}" from "${task.relativeSourceFilePath}"`;
        const modelsLog = `> model id-s: [${item.targetModelIds.map((modelId) => `"${modelId}"`).join(", ")}]`;
        return [targetLog, sourceLog, modelsLog]
            .map((log) => `${indent}${log}`)
            .join("\n");
    }

    export function saveSerializationToDirectory(
        serialization: LightweightSerialization,
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
            writeToFile(toJsonString(item, 2), itemFilePath, (err) => {
                throw Error(
                    `Lightweight serialization failed: failed to save ${itemFilePath} file, ${err.message}`
                );
            });
        }
    }
}
