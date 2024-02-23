import {
    CompletionContext,
    FailureGenerationResult,
    FailureGenerationStatus,
    ProcessEnvironment,
    SourceFileEnvironment,
    SuccessGenerationResult,
    generateCompletion,
} from "../../core/completionGenerator";
import { inspectSourceFile } from "../../core/inspectSourceFile";
import { ProofStep } from "../../coqParser/parsedTypes";
import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { LLMServices, ModelsParams } from "../../llm/configurations";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { Uri } from "../../utils/uri";

import * as path from "path";
import * as assert from "assert";

suite("Benchmark Test", () => {
    test("Complete with `auto`", async () => {
        const filePath = path.join(getTestResourcesDir(), "auto_benchmark.v");
        const modelsParams: ModelsParams = {
            openAiParams: [],
            grazieParams: [],
            predefinedProofsModelParams: [
                {
                    tactics: ["auto."],
                },
            ],
        };
        await runTestBenchmark(filePath, modelsParams);
        console.log("Benchmarking has finished!\n");
    }).timeout(50000);
});

function getTestResourcesDir(): string {
    const dirname: string = path.join(__dirname, "../../../");
    return path.join(dirname, "src", "test", "resources");
}

async function prepareForCompletions(
    modelsParams: ModelsParams,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    filePath: string
): Promise<[CompletionContext[], SourceFileEnvironment, ProcessEnvironment]> {
    const fileUri = Uri.fromPath(filePath);
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig();

    const client = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
    await client.openTextDocument(fileUri);

    const coqProofChecker = new CoqProofChecker(client);
    const mockFileVersion = 1;
    const [completionContexts, sourceFileEnvironment] = await inspectSourceFile(
        mockFileVersion,
        shouldCompleteHole,
        fileUri,
        client
    );
    const llmServices: LLMServices = {
        openAiService: new OpenAiService(),
        grazieService: new GrazieService(),
        predefinedProofsService: new PredefinedProofsService(),
    };
    const processEnvironment: ProcessEnvironment = {
        coqProofChecker: coqProofChecker,
        modelsParams: modelsParams,
        services: llmServices,
    };

    return [completionContexts, sourceFileEnvironment, processEnvironment];
}

async function performSingleCompletion(
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<boolean> {
    const completionPosition = completionContext.admitEndPosition;
    console.log(
        `hole position: ${completionPosition.line}:${completionPosition.character}`
    );
    const result = await generateCompletion(
        completionContext,
        sourceFileEnvironment,
        processEnvironment
    );
    let message = "unknown";
    let success = false;
    if (result instanceof SuccessGenerationResult) {
        message = `success: ${result.data}`;
        success = true;
    } else if (result instanceof FailureGenerationResult) {
        switch (result.status) {
            case FailureGenerationStatus.excededTimeout:
                message = "timeout";
                break;
            case FailureGenerationStatus.exception:
                message = `exception: ${result.message}`;
                break;
            case FailureGenerationStatus.searchFailed:
                message = "no proofs for admit";
                break;
        }
    }
    console.log(message);
    console.log("");
    return success;
}

async function runTestBenchmark(
    filePath: string,
    modelsParams: ModelsParams
): Promise<void> {
    console.log(`run benchmarks for file: ${filePath}`);
    const shouldCompleteHole = (_hole: ProofStep) => true;

    const [completionContexts, sourceFileEnvironment, processEnvironment] =
        await prepareForCompletions(modelsParams, shouldCompleteHole, filePath);

    const totalCompletionsNumber = completionContexts.length;
    let successfulCompletionsNumber = 0;
    for (const completionContext of completionContexts) {
        const success = await performSingleCompletion(
            completionContext,
            sourceFileEnvironment,
            processEnvironment
        );
        if (success) {
            successfulCompletionsNumber += 1;
        }
    }
    console.log(
        `BENCHMARK RESULT: ${successfulCompletionsNumber} / ${totalCompletionsNumber}`
    );
    assert.ok(successfulCompletionsNumber === totalCompletionsNumber);
}
