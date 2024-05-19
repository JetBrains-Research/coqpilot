import { Position } from "vscode-languageclient";

import { LLMSequentialIterator } from "../llm/llmIterator";
import { LLMServices } from "../llm/llmServices";
import { GeneratedProof } from "../llm/llmServices/llmService";
import { ModelsParams } from "../llm/llmServices/modelParams";
import { ProofGenerationContext } from "../llm/proofGenerationContext";

import { Goal, Hyp, PpString } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";
import { EventLogger } from "../logging/eventLogger";

import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";
import {
    CoqLspTimeoutError,
    CoqProofChecker,
    ProofCheckResult,
} from "./coqProofChecker";

export interface CompletionContext {
    proofGoal: Goal<PpString>;
    prefixEndPosition: Position;
    admitEndPosition: Position;
}

export interface SourceFileEnvironment {
    // `fileTheorems` contain only ones that successfully finish with Qed.
    fileTheorems: Theorem[];
    fileLines: string[];
    fileVersion: number;
    dirPath: string;
}

export interface ProcessEnvironment {
    coqProofChecker: CoqProofChecker;
    modelsParams: ModelsParams;
    services: LLMServices;
    /**
     * If `theoremRanker` is not provided, the default one will be used:
     * theorems would be passed sequentially in the same order as they are in the file
     */
    theoremRanker?: ContextTheoremsRanker;
}

export interface GenerationResult {}

export class SuccessGenerationResult implements GenerationResult {
    constructor(public data: any) {}
}

export class FailureGenerationResult implements GenerationResult {
    constructor(
        public status: FailureGenerationStatus,
        public message: string
    ) {}
}

export enum FailureGenerationStatus {
    timeoutExceeded,
    errorOccurred,
    searchFailed,
}

export async function generateCompletion(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    eventLogger?: EventLogger
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
                eventLogger
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
                eventLogger
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
            FailureGenerationStatus.searchFailed,
            "No valid completions found"
        );
    } catch (e: any) {
        const error = e as Error;
        if (error === null) {
            console.error(
                `Object was thrown during completion generation: ${e}`
            );
            return new FailureGenerationResult(
                FailureGenerationStatus.errorOccurred,
                `please report this crash by opening an issue in the Coqpilot GitHub repository: object was thrown as error, "${JSON.stringify(e)}"`
            );
        } else {
            console.error(
                `Error occurred during completion generation: "${error}".\n${error.stack ?? "<no stack available>"}`
            );
        }
        if (e instanceof CoqLspTimeoutError) {
            return new FailureGenerationResult(
                FailureGenerationStatus.timeoutExceeded,
                e.message
            );
        } else {
            return new FailureGenerationResult(
                FailureGenerationStatus.errorOccurred,
                e.message
            );
        }
    }
}

export async function checkAndFixProofs(
    newlyGeneratedProofs: GeneratedProof[],
    sourceFileContentPrefix: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    eventLogger?: EventLogger
): Promise<GeneratedProof[] | SuccessGenerationResult> {
    // check proofs and finish with success if at least one is valid
    const proofCheckResults = await checkGeneratedProofs(
        newlyGeneratedProofs,
        sourceFileContentPrefix,
        completionContext,
        sourceFileEnvironment,
        processEnvironment
    );
    const completion = getFirstValidProof(proofCheckResults);
    if (completion) {
        return new SuccessGenerationResult(completion);
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
                `New proof: ${proof.proof()} with version ${proof.versionNumber()}\n Previous version: ${JSON.stringify(proof.proofVersions.slice(-2))}`
        )
    );
    return fixedProofs; // prepare to a new iteration
}

async function checkGeneratedProofs(
    generatedProofs: GeneratedProof[],
    sourceFileContentPrefix: string[],
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<ProofCheckResult[]> {
    const preparedProofBatch = generatedProofs.map(
        (generatedProof: GeneratedProof) =>
            prepareProofToCheck(generatedProof.proof())
    );
    return processEnvironment.coqProofChecker.checkProofs(
        sourceFileEnvironment.dirPath,
        sourceFileContentPrefix,
        completionContext.prefixEndPosition,
        preparedProofBatch
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
): string | undefined {
    for (const proofCheckResult of proofCheckResults) {
        if (proofCheckResult.isValid) {
            return proofCheckResult.proof;
        }
    }
    return undefined;
}

export function prepareProofToCheck(proof: string) {
    // 1. Remove backtiks -- coq-lsp dies from backticks randomly
    let preparedProof = proof.replace(/`/g, "");

    // 2. Remove Proof. and Qed.
    preparedProof = preparedProof
        .replace(/Proof using\./g, "")
        .replace(/Proof\./g, "")
        .replace(/Qed\./g, "");

    // 3. Wrap proof into { }
    return ` { ${preparedProof} }`;
}

function hypToString(hyp: Hyp<PpString>): string {
    return `${hyp.names.join(" ")} : ${hyp.ty}`;
}

function goalToTargetLemma(proofGoal: Goal<PpString>): string {
    const auxTheoremConcl = proofGoal?.ty;
    const theoremIndeces = proofGoal?.hyps
        .map((hyp) => `(${hypToString(hyp)})`)
        .join(" ");
    return `Lemma helper_theorem ${theoremIndeces} :\n   ${auxTheoremConcl}.`;
}

export function buildProofGenerationContext(
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

export function getTextBeforePosition(
    textLines: string[],
    position: Position
): string[] {
    const textPrefix = textLines.slice(0, position.line + 1);
    textPrefix[position.line] = textPrefix[position.line].slice(
        0,
        position.character
    );
    return textPrefix;
}
