import { ProofGenerationContext } from "../../llm/proofGenerationContext";

import { createTestCoqLspClient } from "../../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../../coqLsp/coqLspClient";

import {
    CompletionContext,
    SourceFileEnvironment,
    TargetType,
} from "../../core/completionGenerationContext";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { buildProofGenerationContext } from "../../core/exposedCompletionGeneratorUtils";
import { inspectSourceFile } from "../../core/inspectSourceFile";

import { ProjectRoot } from "../../utils/structures/projectRoot";
import { Uri } from "../../utils/structures/uri";

import { resolveResourcesDir } from "./pathsResolver";

export interface PreparedEnvironment {
    coqLspClient: CoqLspClient;
    coqProofChecker: CoqProofChecker;
    completionContexts: CompletionContext[];
    sourceFileEnvironment: SourceFileEnvironment;
}

export interface ProjectRootDir {
    path: string[];
    requiresNixEnvironment: boolean;
}

/**
 * Note: both paths should be relative to `src/test/resources/` folder.
 */
export async function withPreparedEnvironment<T>(
    resourcePath: string[],
    projectRootDir: ProjectRootDir | undefined,
    block: (preparedEnvironment: PreparedEnvironment) => Promise<T>
) {
    const [filePath, projectRootPath] = resolveResourcesDir(
        resourcePath,
        projectRootDir?.path
    );
    const fileUri = Uri.fromPath(filePath);
    const projectRoot: ProjectRoot = {
        uri: Uri.fromPath(projectRootPath),
        requiresNixEnvironment: projectRootDir?.requiresNixEnvironment ?? false,
    };

    const client = await createTestCoqLspClient({
        workspaceRootPath: projectRootPath,
    });
    const coqProofChecker = new CoqProofChecker(client);
    try {
        const [completionContexts, sourceFileEnvironment] =
            await client.withTextDocument({ uri: fileUri }, () =>
                inspectSourceFile(
                    1,
                    (_hole) => true,
                    fileUri,
                    projectRoot,
                    client,
                    new AbortController().signal,
                    true, // to support any ranker
                    TargetType.ADMIT // by default
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
    projectRootDir: ProjectRootDir | undefined,
    block: (
        preparedEnvironment: PreparedEnvironment,
        completionContext: CompletionContext,
        proofGenerationContext: ProofGenerationContext
    ) => Promise<T>
): Promise<T> {
    return withPreparedEnvironment(
        resourcePath,
        projectRootDir,
        (environment) =>
            block(
                environment,
                environment.completionContexts[0],
                buildProofGenerationContext(
                    environment.completionContexts[0],
                    environment.sourceFileEnvironment
                )
            )
    );
}
