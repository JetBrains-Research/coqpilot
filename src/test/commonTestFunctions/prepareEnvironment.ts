import { ProofGenerationContext } from "../../llm/proofGenerationContext";

import { CoqLspClient } from "../../coqLsp/coqLspClient";

import {
    CompletionContext,
    SourceFileEnvironment,
    buildProofGenerationContext,
} from "../../core/completionGenerator";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { inspectSourceFile } from "../../core/inspectSourceFile";

import { Uri } from "../../utils/uri";

import { createCoqLspClient } from "./coqLspBuilder";
import { resolveResourcesDir } from "./pathsResolver";

export interface PreparedEnvironment {
    coqLspClient: CoqLspClient;
    coqProofChecker: CoqProofChecker;
    completionContexts: CompletionContext[];
    sourceFileEnvironment: SourceFileEnvironment;
}
/**
 * Note: both paths should be relative to `src/test/resources/` folder.
 */
export async function prepareEnvironment(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<PreparedEnvironment> {
    const [filePath, rootDir] = resolveResourcesDir(
        resourcePath,
        projectRootPath
    );
    const fileUri = Uri.fromPath(filePath);

    const client = await createCoqLspClient(rootDir);
    const coqProofChecker = new CoqProofChecker(client);

    await client.openTextDocument(fileUri);
    const [completionContexts, sourceFileEnvironment] = await inspectSourceFile(
        1,
        (_hole) => true,
        fileUri,
        client
    );
    await client.closeTextDocument(fileUri);

    return {
        coqLspClient: client,
        coqProofChecker: coqProofChecker,
        completionContexts: completionContexts,
        sourceFileEnvironment: sourceFileEnvironment,
    };
}

export async function prepareEnvironmentWithContexts(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<
    [PreparedEnvironment, [CompletionContext, ProofGenerationContext][]]
> {
    const environment = await prepareEnvironment(resourcePath, projectRootPath);
    return [
        environment,
        environment.completionContexts.map((completionContext) => [
            completionContext,
            buildProofGenerationContext(
                completionContext,
                environment.sourceFileEnvironment.fileTheorems
            ),
        ]),
    ];
}
