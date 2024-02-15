import { generateCompletion } from "../../core/completionGenerator";
import * as path from 'path';
import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";
import { inspectSourceFile } from "../../core/inspectSourceFile";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { OpenAiService } from "../../llm/llmService/openai/openAiService";
import { GrazieService } from "../../llm/llmService/grazie/grazieService";
import { PredefinedProofsService } from "../../llm/llmService/predefinedProofs/predefinedProofsService";
import { ProcessEnvironment } from "../../core/completionGenerator";
import { Uri } from "../../utils/uri";

import { 
    FailureGenerationResult, 
    SuccessGenerationResult 
} from "../../core/completionGenerator";

suite('GigaSuite', () => {
	test('MegaTest', async () => {
        const dirname = path.dirname(path.dirname(path.dirname(__dirname)));
        const filePath = path.join(dirname, 'src', 'test', 'resources', 'interaction_test_holes.v');
        const fileUri = Uri.fromPath(filePath);

        const coqLspServerConfig = CoqLspConfig.createServerConfig();
        const coqLspClientConfig = CoqLspConfig.createClientConfig();
        
        const client = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);

        const coqProofChecker = new CoqProofChecker(client);
        await client.openTextDocument(fileUri);
        const [completionContexts, sourceFileEnvironment] = await inspectSourceFile(
            1,
            (_hole) => true,
            fileUri,
            client
        );

        console.log("sourceFileEnvironment: ", sourceFileEnvironment);
        console.log("completionContexts: ", completionContexts);

        const openAiService = new OpenAiService();
        const grazieService = new GrazieService();
        const predefinedProofsService = new PredefinedProofsService();

        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams: {
                openAiParams: [],
                grazieParams: [],
                predefinedProofsModelParams: []
            },
            services: {
                openAiService,
                grazieService,
                predefinedProofsService
            }
        };

        for (const completionContext of completionContexts) {
            const result = await generateCompletion(
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            );
            
            if (result instanceof SuccessGenerationResult) {
                console.log("result: ", result.data);
            } else if (result instanceof FailureGenerationResult) {
                const status = (function() {
                    switch (result.status) {
                        case 0: return "timeout";
                        case 1: return "exception";
                        case 2: return "searchFailed";
                        default: return "unknown";
                    }
                })();
                console.log("result: ", result.message, status);
            } 
        }

    }).timeout(50000);
});





