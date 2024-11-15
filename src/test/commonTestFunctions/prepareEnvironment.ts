import { ProofGenerationContext } from "../../llm/proofGenerationContext";

import { createTestCoqLspClient } from "../../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../../coqLsp/coqLspClient";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../core/completionGenerationContext";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { buildProofGenerationContext } from "../../core/exposedCompletionGeneratorUtils";
import { inspectSourceFile } from "../../core/inspectSourceFile";

import { Uri } from "../../utils/uri";

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
export async function withPreparedEnvironment<T>(
    resourcePath: string[],
    projectRootPath: string[] | undefined,
    block: (preparedEnvironment: PreparedEnvironment) => Promise<T>
) {
    const [filePath, rootDir] = resolveResourcesDir(
        resourcePath,
        projectRootPath
    );
    const fileUri = Uri.fromPath(filePath);

    const client = await createTestCoqLspClient(rootDir);
    const coqProofChecker = new CoqProofChecker(client);
    try {
        const [completionContexts, sourceFileEnvironment] =
            await client.withTextDocument({ uri: fileUri }, () =>
                inspectSourceFile(
                    1,
                    (_hole) => true,
                    fileUri,
                    client,
                    new AbortController().signal
                )
            );
        const preparedEnvironment = {
            coqLspClient: client,
            coqProofChecker: coqProofChecker,
            completionContexts: completionContexts,
            sourceFileEnvironment: sourceFileEnvironment,
        };
        return await block(preparedEnvironment);
    } finally {
        client.dispose();
    }
}

export async function withPreparedEnvironmentAndItsFirstContext<T>(
    resourcePath: string[],
    projectRootPath: string[] | undefined,
    block: (
        preparedEnvironment: PreparedEnvironment,
        completionContext: CompletionContext,
        proofGenerationContext: ProofGenerationContext
    ) => Promise<T>
): Promise<T> {
    return withPreparedEnvironment(
        resourcePath,
        projectRootPath,
        (environment) =>
            block(
                environment,
                environment.completionContexts[0],
                buildProofGenerationContext(
                    environment.completionContexts[0],
                    environment.sourceFileEnvironment.fileTheorems
                )
            )
    );
}
