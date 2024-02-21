import { generateCompletion } from "../../core/completionGenerator";
import * as path from "path";
import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";
import { inspectSourceFile } from "../../core/inspectSourceFile";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { ProcessEnvironment } from "../../core/completionGenerator";
import { Uri } from "../../utils/uri";
import * as assert from "assert";
import { SuccessGenerationResult } from "../../core/completionGenerator";

// More tests will come soon
suite("Simple Test", () => {
    test("Sanity check", async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        const filePath = path.join(
            dirname,
            "src",
            "test",
            "resources",
            "interaction_test_holes.v"
        );
        const fileUri = Uri.fromPath(filePath);

        const coqLspServerConfig = CoqLspConfig.createServerConfig();
        const coqLspClientConfig = CoqLspConfig.createClientConfig();

        const client = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);

        const coqProofChecker = new CoqProofChecker(client);
        await client.openTextDocument(fileUri);
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(1, (_hole) => true, fileUri, client);

        const openAiService = new OpenAiService();
        const grazieService = new GrazieService();
        const predefinedProofsService = new PredefinedProofsService();

        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: {
                openAiParams: [],
                grazieParams: [],
                predefinedProofsModelParams: [
                    {
                        tactics: ["intros.", "auto."],
                    },
                ],
            },
            services: {
                openAiService,
                grazieService,
                predefinedProofsService,
            },
        };

        for (const completionContext of completionContexts) {
            const result = await generateCompletion(
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            );

            assert.ok(result instanceof SuccessGenerationResult);
        }
    }).timeout(50000);
});
