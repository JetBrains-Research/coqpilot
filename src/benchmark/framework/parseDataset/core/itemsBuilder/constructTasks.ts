import { CompletionGenerationTask } from "../../../structures/benchmarkingCore/completionGenerationTask";
import {
    AllTheoremsTarget,
    DatasetInputTargets,
    SpecificTheoremTarget,
} from "../../../structures/common/inputTargets";
import { WorkspaceRoot } from "../../../structures/common/workspaceRoot";
import { ParsedCoqFileData } from "../../../structures/parsedCoqFile/parsedCoqFileData";
import { toTargetType } from "../../../utils/commonStructuresUtils/targetTypeUtils";
import {
    CacheHolderData,
    DatasetCacheHolder,
} from "../../cacheStructures/cacheHolders";

export function constructTasksForBundleTargets(
    requestedTargets: DatasetInputTargets,
    datasetCache: DatasetCacheHolder
): CompletionGenerationTask[] {
    const bundleTasks: CompletionGenerationTask[] = [];

    for (const [
        workspaceRoot,
        workspaceTargets,
    ] of requestedTargets.entries()) {
        const workspaceCache = datasetCache.getWorkspaceCache(
            workspaceRoot.directoryPath
        );
        if (workspaceCache === undefined) {
            throwInsufficientCacheError(
                `workspace ${workspaceRoot.directoryPath}`
            );
        }

        for (const [filePath, fileTargets] of workspaceTargets.entries()) {
            const cachedFile = workspaceCache.getCachedFile(filePath);
            if (cachedFile === undefined) {
                throwInsufficientCacheError(`file ${filePath}`);
            }
            const parsedFileData = cachedFile.restoreParsedCoqFileData();

            for (const fileTarget of fileTargets) {
                if (fileTarget instanceof AllTheoremsTarget) {
                    for (const cachedTheorem of cachedFile.getAllCachedTheorems()) {
                        bundleTasks.push(
                            ...constructTasksForTargetsFromTheorem(
                                cachedTheorem,
                                fileTarget,
                                parsedFileData,
                                workspaceRoot
                            )
                        );
                    }
                } else if (fileTarget instanceof SpecificTheoremTarget) {
                    const cachedTheorem = cachedFile.getCachedTheorem(
                        fileTarget.theoremName
                    );
                    if (cachedTheorem === undefined) {
                        throwInsufficientCacheError(
                            `theorem ${fileTarget.theoremName} from ${filePath}`
                        );
                    }
                    bundleTasks.push(
                        ...constructTasksForTargetsFromTheorem(
                            cachedTheorem,
                            fileTarget,
                            parsedFileData,
                            workspaceRoot
                        )
                    );
                } else {
                    throw Error(
                        `Unknown file target: ${fileTarget.toString("", "")}`
                    );
                }
            }
        }
    }

    return bundleTasks;
}

function constructTasksForTargetsFromTheorem(
    cachedTheorem: CacheHolderData.CachedTheoremData,
    fileTarget: AllTheoremsTarget | SpecificTheoremTarget,
    parsedFileData: ParsedCoqFileData,
    workspaceRoot: WorkspaceRoot
): CompletionGenerationTask[] {
    return cachedTheorem
        .getCachedTargetsByRequestType(fileTarget.requestType)
        .map((cachedTarget) => {
            const goalToProve = cachedTarget.getGoalToProve();
            const targetType = toTargetType(fileTarget.requestType);
            if (goalToProve === undefined) {
                throwInsufficientCacheError(
                    `"${targetType}" target at ${cachedTarget.positionRange.toString()} of theorem ${cachedTheorem.theoremData.name} from ${parsedFileData.filePath}`
                );
            }
            return new CompletionGenerationTask(
                goalToProve,
                cachedTarget.positionRange,
                targetType,
                parsedFileData,
                cachedTheorem.theoremData,
                workspaceRoot
            );
        });
}

function throwInsufficientCacheError(missingObject: string): never {
    const errorMessageLines = [
        "Failed to build benchmarking items: ",
        "invariant failed, updated cache is not sufficient to process requested targets.",
        `\n\tCause: ${missingObject} data is missing.`,
    ];
    throw Error(errorMessageLines.join(""));
}
