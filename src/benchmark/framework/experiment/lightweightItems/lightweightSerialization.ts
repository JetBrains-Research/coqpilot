import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { deserializeCodeElementRange } from "../../structures/common/codeElementPositions";
import { LightweightBenchmarkingItem } from "../../structures/inputParameters/lightweight/lightweightBenchmarkingItem";
import { LightweightInputModelParams } from "../../structures/inputParameters/lightweight/lightweightInputModelParams";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import {
    deserializeGoal,
    goalToProveAsString,
} from "../../utils/coqUtils/goalParser";
import { getTargetTypeName } from "../../utils/serializationUtils";

export namespace LightweightSerialization {
    export interface PackedItems {
        projects: LightweightWorkspaceRoot[];
        models: LightweightInputModelParams[];
        items: LightweightBenchmarkingItem[];
    }

    export function logSerialization(
        openLine: string,
        serialization: LightweightSerialization.PackedItems,
        logger: BenchmarkingLogger
    ) {
        logger
            .asOneRecord()
            .info(openLine)
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
}
