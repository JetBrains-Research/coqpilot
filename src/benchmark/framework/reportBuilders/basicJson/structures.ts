import { GenerationTokens } from "../../../../llm/llmServices/commonStructures/generationTokens";
import { ProofVersion } from "../../../../llm/llmServices/commonStructures/proofVersion";
import { ModelParams } from "../../../../llm/llmServices/modelParams";

import { RankerType } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

import { TargetType } from "../../structures/benchmarkingCore/completionGenerationTask";
import {
    CompletionGenerationTime,
    FailureMetadata,
} from "../../structures/benchmarkingResults/benchmarkedItem";
import { ValidationResult } from "../../structures/benchmarkingResults/benchmarkedProof";
import { SerializedCodeElementRange } from "../../structures/common/codeElementPositions";
import { LLMServiceIdentifier } from "../../structures/common/llmServiceIdentifier";
import { LengthMetrics } from "../../structures/common/measureStructures";
import { LightweightWorkspaceRoot } from "../../structures/inputParameters/lightweight/lightweightWorkspaceRoot";
import { SerializedTheoremsByNames } from "../../structures/parsedCoqFile/parsedCoqFileData";
import { SerializedGoal } from "../../utils/coqUtils/goalParser";

export namespace BasicJsonSerializationStructures {
    export interface SerializedBenchmarkedItem {
        item: SerializedBenchmarkingItem;
        result: SerializedBenchmarkingResult;
    }

    export interface SerializedBenchmarkingItem {
        task: SerializedCompletionGenerationTask;
        params: SerializedBenchmarkingModelParams<ModelParams>;
    }

    export interface SerializedCompletionGenerationTask {
        goalToProve: SerializedGoal;
        positionRange: SerializedCodeElementRange;
        targetType: TargetType;
        parsedSourceFile: SerializedSourceFile;
        sourceTheoremName: string;
        workspaceRoot: LightweightWorkspaceRoot;
    }

    export interface SerializedSourceFile {
        relativePath: string;
        serializedTheoremsByNames: SerializedTheoremsByNames;
        documentVersion: number;
    }

    export interface SerializedBenchmarkingModelParams<
        ResolvedModelParams extends ModelParams,
    > {
        theoremRanker: RankerType;
        modelParams: ResolvedModelParams;
        llmServiceIdentifier: LLMServiceIdentifier;
    }

    export type SerializedBenchmarkingResult =
        | SerializedFailedBenchmarking
        | SerializedSuccessfulBenchmarking;

    export interface SerializedBaseBenchmarkingResult {
        contextTheoremsNames: string[];
        tokensSpentInTotal: GenerationTokens;
        elapsedTime: CompletionGenerationTime;
        round: number;
        parentProofToFixId: number | undefined;
    }

    export interface SerializedFailedBenchmarking
        extends SerializedBaseBenchmarkingResult {
        generatedProofs: SerializedNonValidatedProof[];
        failureMetadata: FailureMetadata;
    }

    export interface SerializedSuccessfulBenchmarking
        extends SerializedBaseBenchmarkingResult {
        generatedProofs: SerializedValidatedProof[];
    }

    export interface SerializedBaseBenchmarkedProof {
        generatedProof: SerializedGeneratedProof;
        asString: string;
        tokensSpent: GenerationTokens;
        length: LengthMetrics;
        generatedProofId: number;
    }

    export interface SerializedNonValidatedProof
        extends SerializedBaseBenchmarkedProof {}

    export interface SerializedValidatedProof
        extends SerializedBaseBenchmarkedProof {
        validationResult: ValidationResult;
    }

    export interface SerializedGeneratedProof {
        proofGenerationContext: SerializedProofGenerationContext;
        previousProofVersions: ProofVersion[];
    }

    export interface SerializedProofGenerationContext {
        completionTarget: string;
        inputContextTheoremsNames: string[];
    }
}
