import { readFileSync } from "fs";
import * as path from "path";

import { CoqLspClient } from "../coqLsp/coqLspClient";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { ProofStep, Theorem } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "./completionGenerationContext";

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
        const goals = await client.getGoalsAtPoint(
            hole.range.start,
            fileUri,
            fileVersion
        );
        if (goals.ok) {
            const firstGoal = goals.val.shift();
            if (firstGoal) {
                completionContexts.push({
                    proofGoal: firstGoal,
                    prefixEndPosition: hole.range.start,
                    admitEndPosition: hole.range.end,
                });
            }
        }
    }

    return completionContexts;
}

export async function createSourceFileEnvironment(
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
