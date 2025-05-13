import { Position } from "vscode-languageclient";

import {
    ExternalPipelineProofGenerationContext,
    ProofGenerationContext,
} from "../llm/proofGenerationContext";

import { Hyp, PpString, ProofGoal } from "../coqLsp/coqLspTypes";

import { relativizeAbsolutePaths } from "../utils/fs/pathUtils";
import { fromRange } from "../utils/structures/codeElementPositions";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "./completionGenerationContext";
import { ContextTheoremsRanker } from "./contextTheoremRanker/contextTheoremsRanker";

export function prepareProofToCheck(proof: string) {
    // 1. Remove backtiks -- coq-lsp dies from backticks randomly
    let preparedProof = proof.replace(/`/g, "");

    // 2. Remove Proof. and Qed.
    preparedProof = preparedProof
        .replace(/Proof using.*?\./g, "")
        .replace(/Proof\./g, "")
        .replace(/Qed\./g, "");

    // 3. Wrap proof into { }
    return ` { ${preparedProof} }`;
}

export function hypToString(hyp: Hyp<PpString>): string {
    return `${hyp.names.join(" ")} : ${hyp.ty}`;
}

export function goalToTargetLemma(proofGoal: ProofGoal): string {
    const auxTheoremConcl = proofGoal?.ty;
    const theoremIndeces = proofGoal?.hyps
        .map((hyp) => `(${hypToString(hyp)})`)
        .join(" ");
    return `Lemma helper_theorem ${theoremIndeces} :\n   ${auxTheoremConcl}.`;
}

export function buildProofGenerationContext(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    theoremRanker?: ContextTheoremsRanker,
    premisesNumber?: number
): ProofGenerationContext {
    const fileTheorems = sourceFileEnvironment.fileTheorems;
    const rankedTheorems =
        theoremRanker
            ?.rankContextTheorems(fileTheorems, completionContext)
            .slice(0, premisesNumber) ?? fileTheorems;
    return {
        contextTheorems: rankedTheorems,
        completionTarget: goalToTargetLemma(completionContext.proofGoal),
        externalPipelineContext: buildExternalPipelineProofGenerationContext(
            completionContext,
            sourceFileEnvironment
        ),
    };
}

export function buildExternalPipelineProofGenerationContext(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment
): ExternalPipelineProofGenerationContext | undefined {
    const projectRoot = sourceFileEnvironment.projectRoot;
    if (projectRoot === undefined) {
        return undefined;
    }
    const projectRootPath = projectRoot.uri.fsPath;
    return {
        completionTargetGoal: completionContext.proofGoal,
        completionTargetRange: fromRange(completionContext.admitRange),

        sourceTheoremName: completionContext.sourceTheorem.name,
        sourceTheoremStatementRange: fromRange(
            completionContext.sourceTheorem.statement_range
        ),
        sourceTheoremProofRange: fromRange(
            completionContext.sourceTheorem.proof.getProofRange()
        ),

        targetType: completionContext.targetType,

        relativeSourceFilePath: relativizeAbsolutePaths(
            projectRootPath,
            sourceFileEnvironment.fileUri.fsPath
        ),
        projectRootPath: projectRootPath,

        requiresNixEnvironment: projectRoot.requiresNixEnvironment,
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
