import { ModelParams } from "../../../../llm/llmServices/modelParams";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import { InputBenchmarkingModelParams } from "../../../../benchmark/framework/experiment/inputBenchmarkingModelParams";
import { BenchmarkingModelParams } from "../../../../benchmark/framework/structures/benchmarkingModelParams";
import {
    SerializedParsedCoqFile,
    deserializeParsedCoqFile,
} from "../../../../benchmark/framework/structures/parsedCoqFileData";
import { SerializedCodeElementRange } from "../../../../benchmark/framework/structures/utilStructures";
import { deserializeGoal } from "../../../../benchmark/framework/utils/goalParser";

export namespace SingleTaskRunnerStructures {
    export interface InputBenchmarkingTask {
        target: CompletionGenerationTarget;
        inputParams: InputBenchmarkingParams;
        workspaceRootDirectoryPath: string | undefined;
    }

    export interface InputBenchmarkingParams {
        llmServiceIdentifier: number; // TODO: stricten
        inputBenchmarkingModelsParams: InputBenchmarkingModelParams.Params;
    }

    export interface BenchmarkingTask {
        target: CompletionGenerationTarget;
        params: BenchmarkingModelParams<ModelParams>;
        workspaceRootDirectoryPath: string | undefined;
        parsedSourceFile: ParsedSourceFile;
    }

    export interface CompletionGenerationTarget {
        goalToProve: string;
        positionRange: SerializedCodeElementRange;
        sourceTheoremName: string;
    }

    // TODO: use new cache structures
    export type ParsedSourceFile = SerializedParsedCoqFile;

    export function buildCompletionContext(
        target: CompletionGenerationTarget
    ): CompletionContext {
        return {
            proofGoal: deserializeGoal(target.goalToProve),
            prefixEndPosition: target.positionRange.start,
            admitEndPosition: target.positionRange.end,
        };
    }

    export function buildSourceFileEnvironment(
        parsedSourceFile: SerializedParsedCoqFile
    ): SourceFileEnvironment {
        return deserializeParsedCoqFile(
            parsedSourceFile
        ).constructSourceFileEnvironment();
    }
}
