import { LLMSequentialIterator } from "../llm/llmIterator";
import { GeneratedProof } from "../llm/llmServices/generatedProof";

import { CoqLspTimeoutError } from "../coqLsp/coqLspTypes";

import { EventLogger } from "../logging/eventLogger";
import { asErrorOrRethrow, buildErrorCompleteLog } from "../utils/errorsUtils";
import { stringifyAnyValue } from "../utils/printers";

import { CompletionAbortError, throwOnAbort } from "./abortUtils";
import {
    CompletionContext,
    ProcessEnvironment,
    SourceFileEnvironment,
} from "./completionGenerationContext";
import { ProofCheckResult } from "./coqProofChecker";
import {
    buildProofGenerationContext,
    prepareProofToCheck,
} from "./exposedCompletionGeneratorUtils";

export interface GenerationResult {}

export class SuccessGenerationResult implements GenerationResult {
    constructor(
        public data: string,
        public attempt: number
    ) {}
}

export class FailureGenerationResult implements GenerationResult {
    constructor(
        public status: FailureGenerationStatus,
        public message: string
    ) {}
}

export enum FailureGenerationStatus {
    TIMEOUT_EXCEEDED,
    ERROR_OCCURRED,
    SEARCH_FAILED,
}

/**
 * _Implementation note:_ when this method is called, the target file is expected to be opened by the user.
 * Therefore, no explicit `coqLspClient.openTextDocument(...)` call is made.
 */
export async function generateCompletion(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    abortSignal: AbortSignal,
    eventLogger?: EventLogger,
    perProofTimeoutMillis: number = 15000
): Promise<GenerationResult> {
    const context = buildProofGenerationContext(
        completionContext,
        sourceFileEnvironment.fileTheorems,
        processEnvironment.theoremRanker,
        processEnvironment.premisesNumber
    );

    eventLogger?.log(
        "proof-gen-context-create",
        "Ranked theorems for proof generation",
        context.contextTheorems.map((thr) => thr.name)
    );
    const iterator = new LLMSequentialIterator(
        context,
        processEnvironment.modelsParams,
        processEnvironment.services,
        eventLogger
    );

    try {
        /** newlyGeneratedProofs = generatedProofsBatch from iterator +
         *  + all proofs fixed at the previous iteration */
        let newlyGeneratedProofs: GeneratedProof[] = [];

        for await (const generatedProofsBatch of iterator) {
            throwOnAbort(abortSignal);
            newlyGeneratedProofs.push(...generatedProofsBatch);
            eventLogger?.log(
                "core-new-proofs-ready-for-checking",
                "Newly generated proofs are ready for checking",
                newlyGeneratedProofs.map(
                    (generatedProof) => generatedProof.proof
                )
            );
            const fixedProofsOrCompletion = await checkAndFixProofs(
                newlyGeneratedProofs,
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                abortSignal,
                eventLogger,
                perProofTimeoutMillis
            );
            if (fixedProofsOrCompletion instanceof SuccessGenerationResult) {
                return fixedProofsOrCompletion;
            }
            newlyGeneratedProofs = [...fixedProofsOrCompletion];
        }

        while (newlyGeneratedProofs.length > 0) {
            throwOnAbort(abortSignal);
            const fixedProofsOrCompletion = await checkAndFixProofs(
                newlyGeneratedProofs,
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                abortSignal,
                eventLogger,
                perProofTimeoutMillis
            );
            if (fixedProofsOrCompletion instanceof SuccessGenerationResult) {
                return fixedProofsOrCompletion;
            }
            newlyGeneratedProofs = [...fixedProofsOrCompletion];
            eventLogger?.log(
                "core-new-proofs-ready-for-checking",
                "Newly generated only proof fixes are ready for checking",
                newlyGeneratedProofs.map(
                    (generatedProof) => generatedProof.proof
                )
            );
        }

        return new FailureGenerationResult(
            FailureGenerationStatus.SEARCH_FAILED,
            "No valid completions found"
        );
    } catch (e: any) {
        const error = asErrorOrRethrow(e);
        console.error(
            `Error occurred during completion generation:\n${buildErrorCompleteLog(error)}`
        );
        if (error instanceof CompletionAbortError) {
            throw error;
        } else if (error instanceof CoqLspTimeoutError) {
            return new FailureGenerationResult(
                FailureGenerationStatus.TIMEOUT_EXCEEDED,
                error.message
            );
        } else {
            return new FailureGenerationResult(
                FailureGenerationStatus.ERROR_OCCURRED,
                error.message
            );
        }
    }
}

async function checkAndFixProofs(
    newlyGeneratedProofs: GeneratedProof[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    abortSignal: AbortSignal,
    eventLogger?: EventLogger,
    perProofTimeoutMillis: number = 15000
): Promise<GeneratedProof[] | SuccessGenerationResult> {
    // check proofs and finish with success if at least one is valid
    const proofCheckResults = await checkGeneratedProofs(
        newlyGeneratedProofs,
        completionContext,
        sourceFileEnvironment,
        processEnvironment,
        perProofTimeoutMillis
    );
    const completion = getFirstValidProof(proofCheckResults);
    if (completion) {
        const [proof, index] = completion;
        return new SuccessGenerationResult(proof, index);
    }

    // fix proofs checked on this iteration
    const proofsWithFeedback: ProofWithFeedback[] = newlyGeneratedProofs.map(
        (generatedProof, i) => {
            return {
                generatedProof: generatedProof,
                diagnostic: proofCheckResults[i].diagnostic!,
            };
        }
    );
    const fixedProofs = await fixProofs(proofsWithFeedback, abortSignal);
    eventLogger?.log(
        "core-proofs-fixed",
        "Proofs were fixed",
        fixedProofs.map(
            (generatedProof) =>
                `New proof: "${generatedProof.proof}" with version ${generatedProof.versionNumber}\n Previous version: ${stringifyAnyValue(generatedProof.proofVersions.slice(-2))}`
        )
    );
    return fixedProofs; // prepare to a new iteration
}

async function checkGeneratedProofs(
    generatedProofs: GeneratedProof[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    perProofTimeoutMillis = 15000
): Promise<ProofCheckResult[]> {
    const preparedProofBatch = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof)
    );

    return processEnvironment.coqProofChecker.checkProofs(
        sourceFileEnvironment.fileUri,
        sourceFileEnvironment.documentVersion,
        completionContext.admitRange.start,
        preparedProofBatch,
        perProofTimeoutMillis
    );
}

interface ProofWithFeedback {
    generatedProof: GeneratedProof;
    diagnostic: string;
}

async function fixProofs(
    proofsWithFeedback: ProofWithFeedback[],
    abortSignal: AbortSignal
): Promise<GeneratedProof[]> {
    const fixProofsPromises = [];

    // build fix promises
    for (const proofWithFeedback of proofsWithFeedback) {
        throwOnAbort(abortSignal);
        const generatedProof = proofWithFeedback.generatedProof;
        if (!generatedProof.canBeFixed()) {
            continue;
        }
        const diagnostic = proofWithFeedback.diagnostic;

        const newProofVersions = generatedProof.fixProof(diagnostic);
        fixProofsPromises.push(newProofVersions);
    }

    // resolve promises: wait for all requested proofs to be fixed
    return (await Promise.allSettled(fixProofsPromises)).flatMap(
        (resolvedPromise) => {
            if (resolvedPromise.status === "fulfilled") {
                return resolvedPromise.value;
            } else {
                console.error(
                    "Failed to fix proof: ",
                    (resolvedPromise as PromiseRejectedResult).reason
                );
                return [];
            }
        }
    );
}

function getFirstValidProof(
    proofCheckResults: ProofCheckResult[]
): [string, number] | undefined {
    let index = 0;
    for (const proofCheckResult of proofCheckResults) {
        if (proofCheckResult.isValid) {
            return [proofCheckResult.proof, index];
        }
        index++;
    }
    return undefined;
}
