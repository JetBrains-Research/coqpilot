import { expect } from "earl";
import * as path from "path";

import { disposeServices } from "../../llm/llmServices";

import {
    FailureGenerationResult,
    FailureGenerationStatus,
    GenerationResult,
    generateCompletion,
} from "../../core/completionGenerator";
import { ProcessEnvironment } from "../../core/completionGenerator";
import { SuccessGenerationResult } from "../../core/completionGenerator";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { inspectSourceFile } from "../../core/inspectSourceFile";

import { Uri } from "../../utils/uri";
import {
    createCoqLspClient,
    createDefaultServices,
    createSinglePredefinedProofsModelsParams,
    getResourceFolder,
} from "../commonTestFunctions";

suite("Completion generation tests", () => {
    async function generateCompletionForAdmitsFromFile(
        resourcePath: string[],
        predefinedProofs: string[],
        projectRootPath?: string[]
    ): Promise<GenerationResult[]> {
        const filePath = path.join(getResourceFolder(), ...resourcePath);
        const rootDir = path.join(
            getResourceFolder(),
            ...(projectRootPath ?? [])
        );

        const fileUri = Uri.fromPath(filePath);
        const client = createCoqLspClient(rootDir);
        const coqProofChecker = new CoqProofChecker(client);
        await client.openTextDocument(fileUri);
        const [completionContexts, sourceFileEnvironment] =
            await inspectSourceFile(1, (_hole) => true, fileUri, client);
        await client.closeTextDocument(fileUri);

        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: coqProofChecker,
            modelsParams:
                createSinglePredefinedProofsModelsParams(predefinedProofs),
            services: createDefaultServices(),
        };
        try {
            return Promise.all(
                completionContexts.map(async (completionContext) => {
                    const result = await generateCompletion(
                        completionContext,
                        sourceFileEnvironment,
                        processEnvironment
                    );

                    return result;
                })
            );
        } finally {
            disposeServices(processEnvironment.services);
        }
    }

    function unpackProof(text: string): string {
        const flatProof = text.replace(/\n/g, " ");
        return flatProof
            .trim()
            .slice(1, flatProof.length - 2)
            .trim();
    }

    test("Check small file with 1 admit", async () => {
        const resourcePath = ["small_document.v"];
        const predefinedProofs = ["intros.", "auto."];

        const results = await generateCompletionForAdmitsFromFile(
            resourcePath,
            predefinedProofs
        );

        expect(results).toHaveLength(1);
        expect(results[0]).toBeA(SuccessGenerationResult);
        expect(
            unpackProof((results[0] as SuccessGenerationResult).data)
        ).toEqual("auto.");
    }).timeout(2000);

    test("Check many admits", async () => {
        const resourcePath = ["test_many_admits.v"];
        const predefinedProofs = ["intros.", "auto."];

        const results = await generateCompletionForAdmitsFromFile(
            resourcePath,
            predefinedProofs
        );

        expect(results).toHaveLength(6);
        for (const result of results) {
            expect(result).toBeA(SuccessGenerationResult);
            expect(
                unpackProof((result as SuccessGenerationResult).data)
            ).toEqual("auto.");
        }
    }).timeout(5000);

    test("Check proofs harder than auto", async () => {
        const resourcePath = ["harder_than_auto.v"];
        const predefinedProofs = [
            "auto.",
            "intros. induction n as [| n' IHn']. { auto. } apply eq_S. apply IHn'.",
        ];

        const results = await generateCompletionForAdmitsFromFile(
            resourcePath,
            predefinedProofs
        );

        expect(results).toHaveLength(2);
        expect(results[0]).toBeA(SuccessGenerationResult);
        expect(
            unpackProof((results[0] as SuccessGenerationResult).data)
        ).toEqual(
            "intros. induction n as [| n' IHn']. { auto. } apply eq_S. apply IHn'."
        );
        expect(results[1]).toBeA(FailureGenerationResult);
        expect((results[1] as FailureGenerationResult).status).toEqual(
            FailureGenerationStatus.searchFailed
        );
    }).timeout(2000);

    test("Check generation in project --non-ci", async () => {
        const resourcePath = ["coqProj", "theories", "C.v"];
        const predefinedProofs = ["intros.", "auto."];
        const projectRootPath = ["coqProj"];

        const results = await generateCompletionForAdmitsFromFile(
            resourcePath,
            predefinedProofs,
            projectRootPath
        );

        expect(results).toHaveLength(1);
        expect(results[0]).toBeA(SuccessGenerationResult);
        expect(
            unpackProof((results[0] as SuccessGenerationResult).data)
        ).toEqual("auto.");
    }).timeout(2000);
});
