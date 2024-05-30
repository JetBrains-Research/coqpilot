import { LLMServiceError } from "../../../../llm/llmServiceErrors";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMService,
} from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../../../../llm/proofGenerationContext";

import {
    CompletionContext,
    FailureGenerationResult,
    FailureGenerationStatus,
    GenerationResult,
    SourceFileEnvironment,
    SuccessGenerationResult,
    getTextBeforePosition,
    goalToTargetLemma,
    prepareProofToCheck,
} from "../../../../core/completionGenerator";
import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";
import {
    CoqProofChecker,
    ProofCheckResult,
} from "../../../../core/coqProofChecker";

import { Theorem } from "../../../../coqParser/parsedTypes";
import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingModelParams } from "../structures/benchmarkingModelParams";

/**
 * TODO: design return info
 * TODO: handle errors properly
 * - (we don't need to catch and wrap all errors into result)
 * - llm service generation / connection error => we need to wait
 * - llm service configuration => skip this task and report
 * - coq proof checker => log proofs, skip this task and report
 */

/**
 * Note: multiround generation is not supported yet.
 */
export async function generateSingleCompletion<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<any, ResolvedModelParams>,
>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMServiceType,
    coqProofChecker: CoqProofChecker
): Promise<GenerationResult> {
    const generatedProofs = await generateProof(
        completionContext,
        sourceFileEnvironment,
        benchmarkingModelParams,
        llmService
    );
    const proofCheckResults = await checkGeneratedProofs(
        generatedProofs,
        completionContext,
        sourceFileEnvironment,
        coqProofChecker
    );

    // TODO: save all valid completions
    const completion = getFirstValidProof(proofCheckResults);
    if (completion) {
        return new SuccessGenerationResult(completion);
    } else {
        return new FailureGenerationResult(
            FailureGenerationStatus.SEARCH_FAILED,
            "No valid completions found"
        );
    }
}

async function generateProof<ResolvedModelParams extends ModelParams>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMService<any, any>
): Promise<GeneratedProof[]> {
    try {
        return await llmService.generateProof(
            buildProofGenerationContext(
                completionContext,
                sourceFileEnvironment.fileTheorems,
                benchmarkingModelParams.theoremRanker
            ),
            benchmarkingModelParams.modelParams,
            benchmarkingModelParams.modelParams.defaultChoices,
            ErrorsHandlingMode.RETHROW_ERRORS
        );
    } catch (e) {
        const llmServiceError = e as LLMServiceError;
        if (llmServiceError === null) {
            throw Error(
                `LLMService is expected to throw only \`LLMServiceError\`-s, but got: ${stringifyAnyValue(e)}`
            );
        }
        // TODO: handle LLMService error
        return [];
    }
}

async function checkGeneratedProofs(
    generatedProofs: GeneratedProof[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    coqProofChecker: CoqProofChecker
): Promise<ProofCheckResult[]> {
    const sourceFileContentPrefix = getTextBeforePosition(
        sourceFileEnvironment.fileLines,
        completionContext.prefixEndPosition
    );
    const preparedProofBatch = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof())
    );
    try {
        return await coqProofChecker.checkProofs(
            sourceFileEnvironment.dirPath,
            sourceFileContentPrefix,
            completionContext.prefixEndPosition,
            preparedProofBatch
        );
    } catch (e) {
        const error = e as Error;
        if (error === null) {
            throw Error(
                `got unexpected error from \`CoqProofChecker\`: ${stringifyAnyValue(e)}`
            );
        }
        // TODO: handle CoqProofChecker error
        // if (error instanceof CoqLspTimeoutError) {
        //     return new FailureGenerationResult(
        //         FailureGenerationStatus.TIMEOUT_EXCEEDED,
        //         error.message
        //     );
        // } else {
        //     return new FailureGenerationResult(
        //         FailureGenerationStatus.ERROR_OCCURRED,
        //         error.message
        //     );
        // }
        return [];
    }
}

function buildProofGenerationContext(
    completionContext: CompletionContext,
    fileTheorems: Theorem[],
    theoremRanker?: ContextTheoremsRanker
): ProofGenerationContext {
    const rankedTheorems =
        theoremRanker?.rankContextTheorems(fileTheorems, completionContext) ??
        fileTheorems;
    return {
        contextTheorems: rankedTheorems,
        completionTarget: goalToTargetLemma(completionContext.proofGoal),
    };
}

function getFirstValidProof(
    proofCheckResults: ProofCheckResult[]
): string | undefined {
    for (const proofCheckResult of proofCheckResults) {
        if (proofCheckResult.isValid) {
            return proofCheckResult.proof;
        }
    }
    return undefined;
}
