import { ModelParams } from "../../proofProviders/impl/modelParams";

import { Theorem } from "../../coqParser/parsedTypes";

export namespace Results {
    export interface BenchmarkingSummary {
        admitsCompletions?: ApproachBenchmarkingSummary;
        theoremsCompletions?: ApproachBenchmarkingSummary;
    }

    export class ApproachBenchmarkingSummary {
        constructor(
            readonly taskToProofProvidersResults: Map<
                CompletionGenerationTask,
                Map<string, ProofProviderBenchmarkingResult<ModelParams>>
            >
        ) {}

        readonly benchmarkingResults = [
            ...this.taskToProofProvidersResults.values(),
        ]
            .flatMap((proofProvidersResults) => [
                ...proofProvidersResults.values(),
            ])
            .flatMap((modelParamsResults) => [...modelParamsResults.values()]);

        readonly successfulBenchmarkingResults =
            this.benchmarkingResults.filter(
                (benchmarkingResult) =>
                    benchmarkingResult.result.successfullyGeneratedCompletion
            );

        allSuccessful(): boolean {
            return (
                this.benchmarkingResults.length ===
                this.successfulBenchmarkingResults.length
            );
        }
    }

    export type ProofProviderBenchmarkingResult<
        ResolvedModelParams extends ModelParams,
    > = Map<ResolvedModelParams, BenchmarkingResult<ResolvedModelParams>>;

    export interface BenchmarkingResult<
        ResolvedModelParams extends ModelParams,
    > {
        task: CompletionGenerationTask;
        proofProviderName: string;
        modelParams: ResolvedModelParams;
        result: CompletionGenerationResult;
    }

    export interface CompletionGenerationTask {
        sourceTheorem: RichTheorem; // RichTheorem(completionContext.paretnTheorem, filePath)
        targetGoal: string; // goalToString(completionContext.proofGoal)
        targetEndPosition: TargetPosition; // admit end / theorem proofSteps[1] position
    }

    // TODO: class with inheritance, maybe abstract
    export interface CompletionGenerationResult {
        successfullyGeneratedCompletion: boolean;
        elapsedTimeMillis: number;
        contextTheorems: RichTheorem[];
        requestChatTokens: number;
    }

    export interface FailedCompletionGenerationResult
        extends CompletionGenerationResult {
        // successfullyGeneratedCompletion: false;
        causeMessage: string; // TODO: enum?
    }

    export interface SuccessfulCompletionGenerationResult
        extends CompletionGenerationResult {
        // TODO: successful = true;
        completionAsString: string;
        completionLength: LengthMetrics;
    }

    export class RichTheorem {
        constructor(
            private readonly theorem: Theorem,
            readonly filePath: string
        ) {}

        readonly name = this.theorem.name;
        readonly proofLength: LengthMetrics = {
            inSteps: this.theorem.proof.proof_steps.length,
        };

        // TODO
        // readonly proofLengthInChars = 0;
        // readonly proofLenghtInTokens = 0;

        // TODO if needed?
        // statement: string,
        // proof: string,
    }

    export interface TargetPosition {
        line: number;
        character: number;
        // toString: ${completionPosition.line}:${completionPosition.character}
        // ctor/func from vscode Position
    }

    export interface LengthMetrics {
        inSteps?: number;
        inChars?: number;
        inTokens?: number;
    }
}
