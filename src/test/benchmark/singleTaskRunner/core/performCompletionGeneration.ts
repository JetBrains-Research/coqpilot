import {
    GeneratedProof,
    LLMService,
} from "../../../../llm/llmServices/llmService";
import { ModelParams } from "../../../../llm/llmServices/modelParams";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";
import { prepareProofToCheck } from "../../../../core/exposedCompletionGeneratorUtils";

import {
    CompletionGenerationTimeImpl,
    MeasuredProofImpl,
} from "../../../../benchmark/framework/benchmarkCompletionGeneration/measureUtils";
import { BenchmarkingLogger } from "../../../../benchmark/framework/logging/benchmarkingLogger";
import {
    BenchmarkedCompletionGeneration,
    CompletionGenerationFailureType,
    FailedCompletionGeneration,
    SuccessfulCompletionGeneration,
} from "../../../../benchmark/framework/structures/benchmarkedItem";
import { BenchmarkingModelParams } from "../../../../benchmark/framework/structures/benchmarkingModelParams";
import { SingleTaskRunnerOptions } from "../runnerOptions";

import { ProofsGeneration } from "./proofsGeneration";
import { ProofsValidation } from "./proofsValidation";

export async function performAndMeasureCompletionGeneration<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<any, ResolvedModelParams>,
>(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    benchmarkingModelParams: BenchmarkingModelParams<ResolvedModelParams>,
    llmService: LLMServiceType,
    workspaceRootDirectoryPath: string | undefined,
    executionOptions: SingleTaskRunnerOptions.BenchmarkingTaskExecutionOptions,
    logger: BenchmarkingLogger
): Promise<BenchmarkedCompletionGeneration> {
    const [generatedProofs, proofsGenerationMillis] =
        await ProofsGeneration.generateProofWithRetriesMeasured(
            completionContext,
            sourceFileEnvironment,
            benchmarkingModelParams,
            llmService,
            executionOptions.requestLLMServiceMaxRetries,
            logger
        );
    logger
        .asOneRecord()
        .info(`Successfully generated ${generatedProofs.length} proofs`)
        .debug(`Effective elapsed time: ${proofsGenerationMillis} ms`, "gray");
    const preparedProofs = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof())
    );
    const measuredTime = new CompletionGenerationTimeImpl(
        proofsGenerationMillis
    );

    let resultMetrics: BenchmarkedCompletionGeneration = {
        allGeneratedProofs: preparedProofs.map(
            (proof) => new MeasuredProofImpl(proof)
        ),
        elapsedTime: measuredTime,
        contextTheorems: undefined, // TODO
        chatTokens: undefined, // TODO
    };

    const proofsValidationResult = await ProofsValidation.checkGeneratedProofs(
        preparedProofs,
        completionContext,
        sourceFileEnvironment,
        workspaceRootDirectoryPath,
        executionOptions.proofsValidationTimeoutMillis,
        logger
    );
    if (ProofsValidation.isFailure(proofsValidationResult)) {
        const failureCauseMessage = proofsValidationResult.causeMessage;
        logger.info(`Failed to validate proofs: ${failureCauseMessage}`);
        return buildFailedCompletionGeneration(
            resultMetrics,
            CompletionGenerationFailureType[proofsValidationResult.failureType],
            failureCauseMessage
        );
    }

    const { proofCheckResults, proofsValidationMillis } =
        proofsValidationResult as ProofsValidation.SuccessResult;
    const validProofs = proofCheckResults
        .filter((checkResult) => checkResult.isValid)
        .map((checkResult) => new MeasuredProofImpl(checkResult.proof));
    measuredTime.addProofsValidationMillis(proofsValidationMillis);
    logger
        .asOneRecord()
        .info(
            `Successfully verified proofs: ${validProofs.length} / ${preparedProofs.length} are valid`
        )
        .debug(`Effective elapsed time: ${proofsValidationMillis} ms`, "gray");

    if (validProofs.length > 0) {
        const successfulGeneration: SuccessfulCompletionGeneration = {
            ...resultMetrics,
            validProofs: validProofs,
        };
        return successfulGeneration;
    } else {
        return buildFailedCompletionGeneration(
            resultMetrics,
            CompletionGenerationFailureType.SEARCH_FAILED,
            "No valid completions found"
        );
    }
}

function buildFailedCompletionGeneration(
    resultMetrics: BenchmarkedCompletionGeneration,
    failureType: CompletionGenerationFailureType,
    causeMessage: string
): FailedCompletionGeneration {
    const failedGeneration: FailedCompletionGeneration = {
        ...resultMetrics,
        failureType: failureType,
        causeMessage: causeMessage,
    };
    return failedGeneration;
}
