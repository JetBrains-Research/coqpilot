import * as path from "path";
import * as tmp from "tmp";

import { LLMServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { GeneratedProof } from "../llm/llmServices/llmService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import { ProofGenerationContext } from "../llm/proofGenerationContext";
import {
    PredefinedProofsUserModelParams,
    UserModelsParams,
} from "../llm/userModelParams";

import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspConfig } from "../coqLsp/coqLspConfig";

import {
    CompletionContext,
    SourceFileEnvironment,
    buildProofGenerationContext,
    getTextBeforePosition,
    prepareProofToCheck,
} from "../core/completionGenerator";
import { CoqProofChecker, ProofCheckResult } from "../core/coqProofChecker";
import { inspectSourceFile } from "../core/inspectSourceFile";

import { parseCoqFile } from "../coqParser/parseCoqFile";
import { Theorem } from "../coqParser/parsedTypes";
import { Uri } from "../utils/uri";

export function testIf(
    condition: boolean,
    testWillBeSkippedCause: string,
    suiteName: string,
    testName: string,
    func: Mocha.Func
): Mocha.Test | undefined {
    if (condition) {
        return test(testName, func);
    }
    console.warn(
        `${color("WARNING", "yellow")}: test will be skipped: \"${suiteName}\" # \"${testName}\"\n\t> cause: ${testWillBeSkippedCause}`
    );
    return undefined;
}

export function getResourcesDir() {
    const dirname = path.dirname(path.dirname(__dirname));
    return path.join(dirname, "src", "test", "resources");
}

export function resolveResourcesDir(
    resourcePath: string[],
    projectRootPath?: string[]
): [string, string] {
    const filePath = path.join(getResourcesDir(), ...resourcePath);
    const rootDir = path.join(getResourcesDir(), ...(projectRootPath ?? []));
    return [filePath, rootDir];
}

export function createCoqLspClient(workspaceRootPath?: string): CoqLspClient {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig(
        process.env.COQ_LSP_PATH || "coq-lsp",
        workspaceRootPath
    );

    return new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
}

export async function parseTheoremsFromCoqFile(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<Theorem[]> {
    const [filePath, rootDir] = resolveResourcesDir(
        resourcePath,
        projectRootPath
    );

    const fileUri = Uri.fromPath(filePath);
    const client = createCoqLspClient(rootDir);

    await client.openTextDocument(fileUri);
    const document = await parseCoqFile(fileUri, client);
    await client.closeTextDocument(fileUri);

    return document;
}

export interface PreparedEnvironment {
    coqLspClient: CoqLspClient;
    coqProofChecker: CoqProofChecker;
    completionContexts: CompletionContext[];
    sourceFileEnvironment: SourceFileEnvironment;
}

// Note: both paths should be relative to `src/test/resources/` folder.
export async function prepareEnvironment(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<PreparedEnvironment> {
    const [filePath, rootDir] = resolveResourcesDir(
        resourcePath,
        projectRootPath
    );
    const fileUri = Uri.fromPath(filePath);

    const client = createCoqLspClient(rootDir);
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

export async function checkProofs(
    proofsToCheck: string[],
    completionContext: CompletionContext,
    environment: PreparedEnvironment
): Promise<ProofCheckResult[]> {
    const sourceFileContentPrefix = getTextBeforePosition(
        environment.sourceFileEnvironment.fileLines,
        completionContext.prefixEndPosition
    );
    return await environment.coqProofChecker.checkProofs(
        environment.sourceFileEnvironment.dirPath,
        sourceFileContentPrefix,
        completionContext.prefixEndPosition,
        proofsToCheck
    );
}

export async function checkTheoremProven(
    generatedProofs: GeneratedProof[],
    completionContext: CompletionContext,
    environment: PreparedEnvironment
) {
    const proofsToCheck = generatedProofs.map((generatedProof) =>
        prepareProofToCheck(generatedProof.proof())
    );
    const checkResults = await checkProofs(
        proofsToCheck,
        completionContext,
        environment
    );
    const validProofs = checkResults.filter(
        (checkResult) => checkResult.isValid
    ).length;
    return validProofs >= 1;
}

export function createDefaultServices(): LLMServices {
    const openAiService = new OpenAiService(tmp.fileSync().name);
    const grazieService = new GrazieService(tmp.fileSync().name);
    const predefinedProofsService = new PredefinedProofsService(
        tmp.fileSync().name
    );
    const lmStudioService = new LMStudioService(tmp.fileSync().name);
    return {
        openAiService,
        grazieService,
        predefinedProofsService,
        lmStudioService,
    };
}

export function createTrivialModelsParams(
    predefinedProofsModelParams: PredefinedProofsUserModelParams[] = []
): UserModelsParams {
    return {
        openAiParams: [],
        grazieParams: [],
        predefinedProofsModelParams: predefinedProofsModelParams,
        lmStudioParams: [],
    };
}

export function createSinglePredefinedProofsModelsParams(
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): UserModelsParams {
    return createTrivialModelsParams([
        createPredefinedProofsModel("predefined-proofs", predefinedProofs),
    ]);
}

export function createPredefinedProofsModel(
    modelName: string = "predefined-proofs",
    predefinedProofs: string[] = [
        "intros.",
        "reflexivity.",
        "auto.",
        "assumption. intros.",
        "left. reflexivity.",
    ]
): PredefinedProofsUserModelParams {
    return {
        modelName: modelName,
        tactics: predefinedProofs,
    };
}

export type Color = "red" | "green" | "yellow" | "blue" | "magenta" | "reset";

export function color(text: string, color: Color): string {
    return `${code(color)}${text}${code("reset")}`;
}

function code(color: Color): string {
    if (color === "reset") {
        return "\x1b[0m";
    }
    if (color === "red") {
        return "\x1b[31m";
    }
    if (color === "green") {
        return "\x1b[32m";
    }
    if (color === "yellow") {
        return "\x1b[33m";
    }
    if (color === "blue") {
        return "\x1b[34m";
    }
    if (color === "magenta") {
        return "\x1b[35m";
    }
    throw Error(`unknown Color: ${color}`);
}
