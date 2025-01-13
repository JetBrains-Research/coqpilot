import { GeneratedProof } from "../../../../llm/llmServices/generatedProof";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import { LightweightSerializer } from "../../experiment/lightweightItems/lightweightSerializer";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingModelParams } from "../../structures/benchmarkingCore/benchmarkingModelParams";
import { CompletionGenerationTask } from "../../structures/benchmarkingCore/completionGenerationTask";
import {
    BenchmarkedItem,
    BenchmarkingResult,
    FailedCompletionGenerationBenchmarking,
    SuccessfulCompletionGenerationBenchmarking,
} from "../../structures/benchmarkingResults/benchmarkedItem";
import {
    BenchmarkedProof,
    NonValidatedProof,
    ValidatedProof,
} from "../../structures/benchmarkingResults/benchmarkedProof";
import { serializeParsedCoqFile } from "../../structures/parsedCoqFile/parsedCoqFileData";

import { BasicJsonSerializationStructures } from "./structures";

/**
 * This serialization is balanced in terms of memory-efficiency and human-readability:
 * it saves `BenchmarkedItem` as a JSON object also providing the following benefits:
 * - keeping sufficient data to fully recover the original object;
 * - saving path-like properties as relative ones;
 * - optimizing common task and parameters data for multiround executions.
 */
export namespace BasicJsonSerialization {
    import Structures = BasicJsonSerializationStructures;

    export function serializeBenchmarkedItem(
        benchmarkedItem: BenchmarkedItem
    ): Structures.SerializedBenchmarkedItem {
        return {
            item: serializeBenchmarkingItem(benchmarkedItem.item),
            result: serializeBenchmarkingResult(benchmarkedItem.result),
        };
    }

    export function serializeBenchmarkingItem(
        benchmarkingItem: BenchmarkingItem
    ): Structures.SerializedBenchmarkingItem {
        return {
            task: serializeCompletionGenerationTask(benchmarkingItem.task),
            params: serializedBenchmarkingModelParams(benchmarkingItem.params),
        };
    }

    export function serializeCompletionGenerationTask(
        task: CompletionGenerationTask
    ): Structures.SerializedCompletionGenerationTask {
        const lightweightTask =
            LightweightSerializer.buildLightweightTask(task);
        const lightweightWorkspaceRoot =
            LightweightSerializer.buildLightweightWorkspaceRoot(
                task.workspaceRoot
            );
        const serializedParsedSourceFile = serializeParsedCoqFile(
            task.parsedSourceFileData
        );

        const serializedSourceFile: Structures.SerializedSourceFile = {
            relativePath: lightweightTask.relativeSourceFilePath,
            serializedTheoremsByNames:
                serializedParsedSourceFile.serializedTheoremsByNames,
            documentVersion: serializedParsedSourceFile.documentVersion,
        };
        const serializedTask: Structures.SerializedCompletionGenerationTask = {
            goalToProve: lightweightTask.goalToProve,
            positionRange: lightweightTask.positionRange,
            targetType: lightweightTask.targetType,
            parsedSourceFile: serializedSourceFile,
            sourceTheoremName: lightweightTask.sourceTheoremName,
            workspaceRoot: lightweightWorkspaceRoot,
        };
        return serializedTask;
    }

    export function serializedBenchmarkingModelParams(
        params: BenchmarkingModelParams<ModelParams>
    ): Structures.SerializedBenchmarkingModelParams<ModelParams> {
        return {
            theoremRanker: params.theoremRanker.type,
            modelParams: params.modelParams,
            llmServiceIdentifier: params.llmServiceIdentifier,
        };
    }

    export function serializeBenchmarkingResult(
        result: BenchmarkingResult
    ): Structures.SerializedBenchmarkingResult {
        const serializedBase: Structures.SerializedBaseBenchmarkingResult = {
            contextTheoremsNames: result.contextTheorems.map(
                (theorem) => theorem.name
            ),
            tokensSpentInTotal: result.tokensSpentInTotal,
            elapsedTime: result.elapsedTime,
            round: result.round,
            parentProofToFixId: result.parentProofToFixId,
        };
        if (result.isSuccessfullyFinishedRound()) {
            return serializeSuccessfulBenchmarking(result, serializedBase);
        }
        return serializeFailedBenchmarking(result, serializedBase);
    }

    function serializeFailedBenchmarking(
        result: FailedCompletionGenerationBenchmarking,
        serializedBase: Structures.SerializedBaseBenchmarkingResult
    ): Structures.SerializedFailedBenchmarking {
        return {
            ...serializedBase,
            generatedProofs: result.generatedProofs.map((proof) =>
                serializeNonValidatedProof(proof)
            ),
            failureMetadata: result.failureMetadata,
        };
    }

    function serializeSuccessfulBenchmarking(
        result: SuccessfulCompletionGenerationBenchmarking,
        serializedBase: Structures.SerializedBaseBenchmarkingResult
    ): Structures.SerializedSuccessfulBenchmarking {
        return {
            ...serializedBase,
            generatedProofs: result.generatedProofs.map((proof) =>
                serializeValidatedProof(proof)
            ),
        };
    }

    export function serializeNonValidatedProof(
        nonValidatedProof: NonValidatedProof
    ): Structures.SerializedNonValidatedProof {
        return serializedBaseBenchmarkedProof(nonValidatedProof);
    }

    export function serializeValidatedProof(
        validatedProof: ValidatedProof
    ): Structures.SerializedValidatedProof {
        return {
            ...serializedBaseBenchmarkedProof(validatedProof),
            validationResult: validatedProof.validationResult,
        };
    }

    function serializedBaseBenchmarkedProof(
        proof: BenchmarkedProof
    ): Structures.SerializedBaseBenchmarkedProof {
        return {
            generatedProof: serializeGeneratedProof(proof.proofObject),
            asString: proof.asString,
            tokensSpent: proof.tokensSpent,
            length: proof.length,
            generatedProofId: proof.generatedProofId,
        };
    }

    export function serializeGeneratedProof(
        proofObject: GeneratedProof
    ): Structures.SerializedGeneratedProof {
        return {
            proofGenerationContext: serializeProofGenerationContext(
                proofObject.proofGenerationContext
            ),
            previousProofVersions: proofObject.proofVersions,
        };
    }

    export function serializeProofGenerationContext(
        proofGenerationContext: ProofGenerationContext
    ): Structures.SerializedProofGenerationContext {
        return {
            completionTarget: proofGenerationContext.completionTarget,
            inputContextTheoremsNames:
                proofGenerationContext.contextTheorems.map(
                    (theorem) => theorem.name
                ),
        };
    }
}
