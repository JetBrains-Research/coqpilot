import { DocumentUri } from "vscode-languageclient";
import { parseCoqFile } from "../coqParser/parseCoqFile";
import { CoqLspClient } from "../coqLsp/coqLspClient";
import { readFileSync } from "fs";
import { 
    ProofStep,
    Theorem
} from "../coqParser/parsedTypes";
import * as path from 'path';

import { 
    CompletionContext, 
    SourceFileEnvironment
} from "./completionGenerator";

type AnalyzedFile = [SourceFileEnvironment, CompletionContext[]]; 

export async function inspectSourceFile(
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: DocumentUri, 
    client: CoqLspClient,
): Promise<AnalyzedFile> {
    const sourceFileEnvironment = await createSourceFileEnvironment(fileUri, client);
    const completionContexts = await createCompletionContexts(
        shouldCompleteHole, 
        sourceFileEnvironment.fileTheorems,
        fileUri,
        client
    );

    return [sourceFileEnvironment, completionContexts];
}

async function createCompletionContexts(
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileTheorems: Theorem[],
    fileUri: DocumentUri,
    client: CoqLspClient
): Promise<CompletionContext[]> {
    const holesToComplete = fileTheorems
        .filter((thr) => thr.proof)
        .map((thr) => thr.proof!.holes)
        .flat()
        .filter(shouldCompleteHole);

    // TODO: Figure out if we need the correct version here
    let completionContexts: CompletionContext[] = [];
    for (const hole of holesToComplete) {
        const goal = await client.getFirstGoalAtPoint(
            hole.range.start,
            fileUri,
            65
        );
        if (!(goal instanceof Error)) {
            completionContexts.push({
                proofGoal: goal,
                prefixEndPosition: hole.range.start
            });
        }
    }

    return completionContexts;
}

async function createSourceFileEnvironment(
    fileUri: DocumentUri, 
    client: CoqLspClient
): Promise<SourceFileEnvironment> {
    const fileTheorems = await parseCoqFile(fileUri, client);
    const fileText = readFileSync(fileUri);
    const dirPath = getSourceFolderPath(fileUri);
    if (!dirPath) {
        throw new Error("Unable to get source folder path");
    }

    return {
        fileTheorems: fileTheorems,
        fileLines: fileText.toString().split('\n'),
        dirPath: dirPath
    };
}

function getSourceFolderPath(documentUri: string): string | undefined {
    try {
        if (documentUri.startsWith('file:///')) {
            const fsPath = decodeURI(documentUri.substring('file:///'.length));
            const sourceFolderPath = path.dirname(fsPath);

            return sourceFolderPath;
        } else {
            return undefined;
        }
    } catch (error) {
        return undefined;
    }
}