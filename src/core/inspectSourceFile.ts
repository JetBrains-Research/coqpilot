import { readFileSync } from "fs";

import { CoqLspClientInterface } from "../coqLsp/coqLspClient";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { ProofStep, Theorem } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "./completionGenerationContext";

type AnalyzedFile = [CompletionContext[], SourceFileEnvironment];

export async function inspectSourceFile(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri,
    client: CoqLspClientInterface,
    rankerNeedsInitialGoals: boolean = true
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        documentVersion,
        fileUri,
        client,
        rankerNeedsInitialGoals
    );
    const completionContexts = await createCompletionContexts(
        documentVersion,
        shouldCompleteHole,
        sourceFileEnvironment.fileTheorems,
        fileUri,
        client
    );
    const sourceFileEnvironmentWithCompleteProofs: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => thr.proof && !thr.proof.is_incomplete
        ),
    };

    return [completionContexts, sourceFileEnvironmentWithCompleteProofs];
}

async function createCompletionContexts(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileTheorems: Theorem[],
    fileUri: Uri,
    client: CoqLspClientInterface
): Promise<CompletionContext[]> {
    const holesToComplete = fileTheorems
        .filter((thr) => thr.proof)
        .map((thr) => thr.proof!.holes)
        .flat()
        .filter(shouldCompleteHole);

    let completionContexts: CompletionContext[] = [];
    for (const hole of holesToComplete) {
        const goals = await client.getGoalsAtPoint(
            hole.range.start,
            fileUri,
            documentVersion
        );
        if (goals.ok) {
            const firstGoal = goals.val.shift();
            if (firstGoal) {
                completionContexts.push({
                    proofGoal: firstGoal,
                    admitRange: hole.range,
                });
            }
        }
    }

    return completionContexts;
}

export async function createSourceFileEnvironment(
    documentVersion: number,
    fileUri: Uri,
    client: CoqLspClientInterface,
    rankerNeedsInitialGoals: boolean = true
): Promise<SourceFileEnvironment> {
    const fileTheorems = await parseCoqFile(
        fileUri,
        client,
        rankerNeedsInitialGoals
    );
    const fileText = readFileSync(fileUri.fsPath);

    return {
        fileTheorems: fileTheorems,
        fileLines: fileText.toString().split("\n"),
        documentVersion: documentVersion,
        fileUri: fileUri,
    };
}