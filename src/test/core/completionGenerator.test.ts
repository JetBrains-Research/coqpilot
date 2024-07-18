import { expect } from "earl";

import { disposeServices } from "../../llm/llmServices";

import { ProcessEnvironment } from "../../core/completionGenerationContext";
import {
    FailureGenerationResult,
    FailureGenerationStatus,
    GenerationResult,
    generateCompletion,
} from "../../core/completionGenerator";
import { SuccessGenerationResult } from "../../core/completionGenerator";

import {
    createDefaultServices,
    createPredefinedProofsModelsParams,
} from "../commonTestFunctions/defaultLLMServicesBuilder";
import { prepareEnvironment } from "../commonTestFunctions/prepareEnvironment";

suite("Completion generation tests", () => {
    async function generateCompletionForAdmitsFromFile(
        resourcePath: string[],
        predefinedProofs: string[],
        projectRootPath?: string[]
    ): Promise<GenerationResult[]> {
        const environment = await prepareEnvironment(
            resourcePath,
            projectRootPath
        );
        const processEnvironment: ProcessEnvironment = {
            coqProofChecker: environment.coqProofChecker,
            modelsParams: createPredefinedProofsModelsParams(predefinedProofs),
            services: createDefaultServices(),
        };
        try {
            return await Promise.all(
                environment.completionContexts.map(
                    async (completionContext) => {
                        const result = await generateCompletion(
                            completionContext,
                            environment.sourceFileEnvironment,
                            processEnvironment,
                            () => {}
                        );
                        return result;
                    }
                )
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
    }).timeout(5000);

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
    }).timeout(30000);

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
            FailureGenerationStatus.SEARCH_FAILED
        );
    }).timeout(5000);

    test("Check generation in project", async () => {
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
    }).timeout(5000);
});
