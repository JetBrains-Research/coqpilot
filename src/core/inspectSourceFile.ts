import { readFileSync } from "fs";
import * as path from "path";

import { CoqLspClient } from "../coqLsp/coqLspClient";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { ProofStep, Theorem, TheoremProof } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "./completionGenerator";

type AnalyzedFile = [CompletionContext[], SourceFileEnvironment];

export async function inspectSourceFile(
    fileVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri,
    client: CoqLspClient
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        fileVersion,
        fileUri,
        client
    );
    const completionContexts = await createCompletionContexts(
        fileVersion,
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

export async function inspectSourceShortening(
    fileVersion: number,
    shouldShortenProof: (proof: TheoremProof) => boolean,
    fileUri: Uri,
    client: CoqLspClient
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        fileVersion,
        fileUri,
        client
    );
    const completionContexts = await createSohrteningContexts(
        fileVersion,
        shouldShortenProof,
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
    fileVersion: number,
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
        const goal = await client.getFirstGoalAtPoint(
            hole.range.start,
            fileUri,
            fileVersion
        );
        if (!(goal instanceof Error)) {
            completionContexts.push({
                proofGoal: goal,
                prefixEndPosition: hole.range.start,
                admitEndPosition: hole.range.end,
            });
        }
    }

    return completionContexts;
}

async function createSohrteningContexts(
    fileVersion: number,
    shouldShortenProof: (proof: TheoremProof) => boolean,
    fileTheorems: Theorem[],
    fileUri: Uri,
    client: CoqLspClient
): Promise<CompletionContext[]> {
    const proofsToShorten = fileTheorems
        .filter((thr) => thr.proof)
        .map((thr) => thr.proof!)
        .filter(shouldShortenProof);

    let completionContexts: CompletionContext[] = [];
    if (proofsToShorten.length != 1) {
        return completionContexts;
    }

    const proofToShorten = proofsToShorten[0];

    const goal = await client.getFirstGoalAtPoint(
        proofToShorten.proof_range.start,
        fileUri,
        fileVersion
    );
    if (!(goal instanceof Error)) {
        completionContexts.push({
            proofGoal: goal,
            prefixEndPosition: proofToShorten.proof_range.start,
            admitEndPosition: proofToShorten.proof_range.end,
        });
    }
    

    return completionContexts;
}

async function createSourceFileEnvironment(
    fileVersion: number,
    fileUri: Uri,
    client: CoqLspClient
): Promise<SourceFileEnvironment> {
    const fileTheorems = await parseCoqFile(fileUri, client);
    const fileText = readFileSync(fileUri.fsPath);
    const dirPath = getSourceFolderPath(fileUri);
    if (!dirPath) {
        throw Error(
            `unable to get source folder path from \`fileUri\`: ${fileUri}`
        );
    }

    return {
        fileTheorems: fileTheorems,
        fileLines: fileText.toString().split("\n"),
        fileVersion: fileVersion,
        dirPath: dirPath,
    };
}

function getSourceFolderPath(documentUri: Uri): string | undefined {
    try {
        return path.dirname(documentUri.fsPath);
    } catch (error) {
        return undefined;
    }
}
