import { LLMSequentialIterator } from "../llm/llmIterator";
import { ModelsParams, LLMServices } from "../llm/configurations";

import {
    CoqProofChecker,
    ProofCheckResult,
    CoqLspTimeoutError,
} from "./coqProofChecker";

import { ProofGenerationContext } from "../llm/llmServices/modelParamsInterfaces";
import { EventLogger } from "../logging/eventLogger";
import { Position } from "vscode-languageclient";
import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";

import { Hyp, Goal, PpString } from "../coqLsp/coqLspTypes";

import { Theorem } from "../coqParser/parsedTypes";

export interface CompletionContext {
    proofGoal: Goal<PpString>;
    prefixEndPosition: Position;
    admitEndPosition: Position;
}

export interface SourceFileEnvironment {
    // Theorems here are only those that
    // successfully finish with Qed.
    fileTheorems: Theorem[];
    fileLines: string[];
    fileVersion: number;
    dirPath: string;
}

export interface ProcessEnvironment {
    coqProofChecker: CoqProofChecker;
    modelsParams: ModelsParams;
    services: LLMServices;
    // If not provided, the default ranker will be used:
    // Theorems would be passed sequentially
    // in the same order as they are in the file
    theoremRanker?: ContextTheoremsRanker;
}

export async function generateCompletion(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    eventLogger?: EventLogger
): Promise<GenerationResult> {
    const context = buildProofGenerationContext(
        completionContext,
        sourceFileEnvironment,
        processEnvironment
    );
    eventLogger?.log(
        "proof-gen-context-create",
        "Ranked theorems for proof generation",
        context.sameFileTheorems.map((thr) => thr.name)
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
        for await (const proofBatch of iterator) {
            const praparedProofBatch = proofBatch.map((proof: string) =>
                prepareProofToCheck(proof)
            );
            const proofCheckResults =
                await processEnvironment.coqProofChecker.checkProofs(
                    sourceFileEnvironment.dirPath,
                    sourceFileContentPrefix,
                    completionContext.prefixEndPosition,
                    praparedProofBatch
                );

            const completion = getFirstValidProof(proofCheckResults);
            if (completion) {
                return new SuccessGenerationResult(completion);
            }
        }

        return new FailureGenerationResult(
            FailureGenerationStatus.searchFailed,
            "No valid completions found"
        );
    } catch (e: any) {
        if (e instanceof CoqLspTimeoutError) {
            return new FailureGenerationResult(
                FailureGenerationStatus.excededTimeout,
                e.message
            );
        } else {
            return new FailureGenerationResult(
                FailureGenerationStatus.exception,
                e.message
            );
        }
    }
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
    excededTimeout,
    exception,
    searchFailed,
}

function getFirstValidProof(
    proofCheckResults: ProofCheckResult[]
): string | undefined {
    for (const [proof, isValid, _message] of proofCheckResults) {
        if (isValid) {
            return proof;
        }
    }

    return undefined;
}

function prepareProofToCheck(proof: string) {
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

function buildProofGenerationContext(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): ProofGenerationContext {
    const rankedTheorems =
        processEnvironment.theoremRanker?.rankContextTheorems(
            sourceFileEnvironment.fileTheorems,
            completionContext
        ) ?? sourceFileEnvironment.fileTheorems;
    return {
        sameFileTheorems: rankedTheorems,
        admitCompletionTarget: goalToTargetLemma(completionContext.proofGoal),
    };
}

function getTextBeforePosition(
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
