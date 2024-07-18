import { LLMSequentialIterator } from "../llm/llmIterator";
import { GeneratedProof } from "../llm/llmServices/llmService";

import { EventLogger } from "../logging/eventLogger";
import { stringifyAnyValue } from "../utils/printers";

import {
    CompletionContext,
    ProcessEnvironment,
    SourceFileEnvironment,
} from "./completionGenerationContext";
import { CoqLspTimeoutError, ProofCheckResult } from "./coqProofChecker";
import {
    buildProofGenerationContext,
    getTextBeforePosition,
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

export async function generateCompletion(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    repairProcessEnvironmentBeforeEachProofsCheck: (
        processEnvironment: ProcessEnvironment
    ) => void,
    eventLogger?: EventLogger,
    workspaceRootPath?: string,
    perProofTimeoutMillis: number = 15000
): Promise<GenerationResult> {
    const context = buildProofGenerationContext(
        completionContext,
        sourceFileEnvironment.fileTheorems,
        processEnvironment.theoremRanker
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
    const sourceFileContentPrefix = getTextBeforePosition(
        sourceFileEnvironment.fileLines,
        completionContext.prefixEndPosition
    );

    try {
        /** newlyGeneratedProofs = generatedProofsBatch from iterator +
         *  + all proofs fixed at the previous iteration */
        let newlyGeneratedProofs: GeneratedProof[] = [];

        for await (const generatedProofsBatch of iterator) {
            newlyGeneratedProofs.push(...generatedProofsBatch);
            eventLogger?.log(
                "core-new-proofs-ready-for-checking",
                "Newly generated proofs are ready for checking",
                newlyGeneratedProofs.map((proof) => proof.proof())
            );
            const fixedProofsOrCompletion = await checkAndFixProofs(
                newlyGeneratedProofs,
                sourceFileContentPrefix,
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                repairProcessEnvironmentBeforeEachProofsCheck,
                eventLogger,
                workspaceRootPath,
                perProofTimeoutMillis
            );
            if (fixedProofsOrCompletion instanceof SuccessGenerationResult) {
                return fixedProofsOrCompletion;
            }
            newlyGeneratedProofs = [...fixedProofsOrCompletion];
        }

        while (newlyGeneratedProofs.length > 0) {
            const fixedProofsOrCompletion = await checkAndFixProofs(
                newlyGeneratedProofs,
                sourceFileContentPrefix,
                completionContext,
                sourceFileEnvironment,
                processEnvironment,
                repairProcessEnvironmentBeforeEachProofsCheck,
                eventLogger,
                workspaceRootPath,
                perProofTimeoutMillis
            );
            if (fixedProofsOrCompletion instanceof SuccessGenerationResult) {
                return fixedProofsOrCompletion;
            }
            newlyGeneratedProofs = [...fixedProofsOrCompletion];
            eventLogger?.log(
                "core-new-proofs-ready-for-checking",
                "Newly generated only proof fixes are ready for checking",
                newlyGeneratedProofs.map((proof) => proof.proof())
            );
        }

        return new FailureGenerationResult(
            FailureGenerationStatus.SEARCH_FAILED,
            "No valid completions found"
        );
    } catch (e: any) {
        const error = e as Error;
        if (error === null) {
            console.error(
                `Object was thrown during completion generation: ${e}`
            );
            return new FailureGenerationResult(
                FailureGenerationStatus.ERROR_OCCURRED,
                `please report this crash by opening an issue in the Coqpilot GitHub repository: object was thrown as error, ${stringifyAnyValue(e)}`
            );
        } else {
            console.error(
                `Error occurred during completion generation:\n${error.stack ?? error}`
            );
        }
        if (e instanceof CoqLspTimeoutError) {
            return new FailureGenerationResult(
                FailureGenerationStatus.TIMEOUT_EXCEEDED,
                e.message
            );
        } else {
            return new FailureGenerationResult(
                FailureGenerationStatus.ERROR_OCCURRED,
                e.message
            );
        }
    }
}

async function checkAndFixProofs(
    newlyGeneratedProofs: GeneratedProof[],
    sourceFileContentPrefix: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    repairProcessEnvironmentBeforeEachProofsCheck: (
        processEnvironment: ProcessEnvironment
    ) => void,
    eventLogger?: EventLogger,
    workspaceRootPath?: string,
    perProofTimeoutMillis: number = 15000
): Promise<GeneratedProof[] | SuccessGenerationResult> {
    // check proofs and finish with success if at least one is valid
    const proofCheckResults = await checkGeneratedProofs(
        newlyGeneratedProofs,
        sourceFileContentPrefix,
        completionContext,
        sourceFileEnvironment,
        processEnvironment,
        repairProcessEnvironmentBeforeEachProofsCheck,
        workspaceRootPath,
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
    const fixedProofs = await fixProofs(proofsWithFeedback);
    eventLogger?.log(
        "core-proofs-fixed",
        "Proofs were fixed",
        fixedProofs.map(
            (proof) =>
                `New proof: "${proof.proof()}" with version ${proof.versionNumber()}\n Previous version: ${stringifyAnyValue(proof.proofVersions.slice(-2))}`
        )
    );
    return fixedProofs; // prepare to a new iteration
}

async function checkGeneratedProofs(
    generatedProofs: GeneratedProof[],
    sourceFileContentPrefix: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    repairProcessEnvironmentBeforeEachProofsCheck: (
        processEnvironment: ProcessEnvironment
    ) => void,
    workspaceRootPath?: string,
    perProofTimeoutMillis = 15000
): Promise<ProofCheckResult[]> {
    const preparedProofBatch = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof())
    );

    if (workspaceRootPath) {
        repairProcessEnvironmentBeforeEachProofsCheck(processEnvironment);
    }

    return processEnvironment.coqProofChecker.checkProofs(
        sourceFileEnvironment.dirPath,
        sourceFileContentPrefix,
        completionContext.prefixEndPosition,
        preparedProofBatch,
        perProofTimeoutMillis
    );
}

interface ProofWithFeedback {
    generatedProof: GeneratedProof;
    diagnostic: string;
}

async function fixProofs(
    proofsWithFeedback: ProofWithFeedback[]
): Promise<GeneratedProof[]> {
    const fixProofsPromises = [];

    // build fix promises
    for (const proofWithFeedback of proofsWithFeedback) {
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
