import { CoqLspClient } from "../coqLsp/coqLspClient";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { ProofStep, Theorem } from "../coqParser/parsedTypes";
import { EventLogger } from "../logging/eventLogger";
import { ProjectRoot } from "../utils/structures/projectRoot";
import { Uri } from "../utils/structures/uri";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "./completionGenerationContext";

type AnalyzedFile = [CompletionContext[], SourceFileEnvironment];

export async function inspectSourceFile(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri,
    projectRoot: ProjectRoot | undefined,
    client: CoqLspClient,
    abortSignal: AbortSignal,
    needsTheoremInitialGoals: boolean,
    eventLogger?: EventLogger
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        documentVersion,
        fileUri,
        projectRoot,
        client,
        abortSignal,
        needsTheoremInitialGoals,
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
    let completionContexts: CompletionContext[] = [];
    for (const thr of fileTheorems) {
        for (const hole of thr.proof.holes) {
            if (!shouldCompleteHole(hole)) {
                continue;
            }
            const goals = await client.getGoalsAtPoint(
                hole.range.start,
                fileUri,
                documentVersion
            );
            if (goals.ok && goals.val.length !== 0) {
                completionContexts.push({
                    proofGoal: goals.val[0],
                    admitRange: hole.range,
                    sourceTheorem: thr,
                });
            }
        }
    }
    return completionContexts;
}

export async function createSourceFileEnvironment(
    documentVersion: number,
    fileUri: Uri,
    projectRoot: ProjectRoot | undefined,
    client: CoqLspClient,
    abortSignal: AbortSignal,
    needsTheoremInitialGoals: boolean,
    eventLogger?: EventLogger
): Promise<SourceFileEnvironment> {
    const fileTheorems = await parseCoqFile(
        fileUri,
        client,
        abortSignal,
        needsTheoremInitialGoals,
        eventLogger
    );

    return {
        fileTheorems: fileTheorems,
        documentVersion: documentVersion,
        fileUri: fileUri,
        projectRoot: projectRoot,
    };
}
