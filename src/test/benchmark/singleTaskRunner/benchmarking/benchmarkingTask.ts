import * as path from "path";

import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { Goal, PpString } from "../../../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import { InputBenchmarkingModelParams } from "../../../../benchmark/framework/experiment/inputBenchmarkingModelParams";
import { BenchmarkingModelParams } from "../../../../benchmark/framework/structures/benchmarkingModelParams";
import { SerializedParsedCoqFile } from "../../../../benchmark/framework/structures/parsedCoqFileData";
import { deserializeTheorem } from "../../../../benchmark/framework/structures/theoremData";
import { SerializedCodeElementRange } from "../../../../benchmark/framework/structures/utilStructures";

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
        goalToProve: any; // JSON.parse(JSON.stringify(...))
        positionRange: SerializedCodeElementRange;
        sourceTheoremName: string;
    }

    // TODO: create a separate type (with relative file path)
    export type ParsedSourceFile = SerializedParsedCoqFile;

    export function buildCompletionContext(
        target: CompletionGenerationTarget
    ): CompletionContext {
        return {
            proofGoal: target.goalToProve as Goal<PpString>,
            prefixEndPosition: target.positionRange.start,
            admitEndPosition: target.positionRange.end,
        };
    }

    export function buildSourceFileEnvironment(
        parsedSourceFile: SerializedParsedCoqFile
    ): SourceFileEnvironment {
        return {
            fileTheorems: parsedSourceFile.allFileTheorems
                .filter(
                    (serializedTheorem) =>
                        serializedTheorem.proof &&
                        !serializedTheorem.proof.is_incomplete
                )
                .map((serializedTheorem) =>
                    deserializeTheorem(serializedTheorem)
                ),
            fileLines: parsedSourceFile.fileLines,
            fileVersion: parsedSourceFile.fileVersion,
            dirPath: path.dirname(parsedSourceFile.filePath),
        };
    }
}
