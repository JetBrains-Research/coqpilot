import { parseCoqFile } from "../coqParser/parseCoqFile";
import { CoqLspClient } from "../coqLsp/coqLspClient";
import { readFileSync } from "fs";
import { Uri } from "../utils/uri";
import { 
    ProofStep,
    Theorem
} from "../coqParser/parsedTypes";
import * as path from 'path';

import { 
    CompletionContext, 
    SourceFileEnvironment
} from "./completionGenerator";

type AnalyzedFile = [CompletionContext[], SourceFileEnvironment]; 

export async function inspectSourceFile(
    fileVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri, 
    client: CoqLspClient,
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(fileVersion, fileUri, client);
    const completionContexts = await createCompletionContexts(
        fileVersion,
        shouldCompleteHole, 
        sourceFileEnvironment.fileTheorems,
        fileUri,
        client
    );

    return [completionContexts, sourceFileEnvironment];
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
                admitEndPosition: hole.range.end
            });
        }
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
        throw new Error("Unable to get source folder path");
    }

    return {
        fileTheorems: fileTheorems,
        fileLines: fileText.toString().split('\n'),
        fileVersion: fileVersion,
        dirPath: dirPath
    };
}

function getSourceFolderPath(documentUri: Uri): string | undefined {
    try {
        return path.dirname(documentUri.fsPath);
    } catch (error) {
        return undefined;
    }
}