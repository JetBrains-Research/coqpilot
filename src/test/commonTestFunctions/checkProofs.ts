import { GeneratedProof } from "../../llm/llmServices/llmService";

import { CompletionContext } from "../../core/completionGenerationContext";
import { ProofCheckResult } from "../../core/coqProofChecker";
import { prepareProofToCheck } from "../../core/exposedCompletionGeneratorUtils";
import { getTextBeforePosition } from "../../core/exposedCompletionGeneratorUtils";

import { PreparedEnvironment } from "./prepareEnvironment";

export async function checkProofs(
    proofsToCheck: string[],
    completionContext: CompletionContext,
    environment: PreparedEnvironment
): Promise<ProofCheckResult[]> {
    const sourceFileContentPrefix = getTextBeforePosition(
        environment.sourceFileEnvironment.fileLines,
        completionContext.prefixEndPosition
    );
    return await environment.coqProofChecker.checkProofs(
        environment.sourceFileEnvironment.dirPath,
        sourceFileContentPrefix,
        completionContext.prefixEndPosition,
        proofsToCheck
    );
}

export async function checkTheoremProven(
    generatedProofs: GeneratedProof[],
    completionContext: CompletionContext,
    environment: PreparedEnvironment
) {
    const proofsToCheck = generatedProofs.map((generatedProof) =>
        prepareProofToCheck(generatedProof.proof())
    );
    const checkResults = await checkProofs(
        proofsToCheck,
        completionContext,
        environment
    );
    const validProofs = checkResults.filter(
        (checkResult) => checkResult.isValid
    ).length;
    return validProofs >= 1;
}
