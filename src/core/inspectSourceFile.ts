import { CoqLspClient } from "../coqLsp/coqLspClient";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { ProofStep, Theorem } from "../coqParser/parsedTypes";
import { EventLogger } from "../logging/eventLogger";
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
    client: CoqLspClient,
    abortSignal: AbortSignal,
    rankerNeedsInitialGoals: boolean = true,
    eventLogger?: EventLogger
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        documentVersion,
        fileUri,
        client,
        abortSignal,
        rankerNeedsInitialGoals,
        eventLogger
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
            (thr) => !thr.proof.is_incomplete
        ),
    };

    return [completionContexts, sourceFileEnvironmentWithCompleteProofs];
}

async function createCompletionContexts(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileTheorems: Theorem[],
    fileUri: Uri,
    client: CoqLspClient
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
    client: CoqLspClient,
    abortSignal: AbortSignal,
    rankerNeedsInitialGoals: boolean = true,
    eventLogger?: EventLogger
): Promise<SourceFileEnvironment> {
    const fileTheorems = await parseCoqFile(
        fileUri,
        client,
        abortSignal,
        rankerNeedsInitialGoals,
        eventLogger
    );

    return {
        fileTheorems: fileTheorems,
        documentVersion: documentVersion,
        fileUri: fileUri,
    };
}
