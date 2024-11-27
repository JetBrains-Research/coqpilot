import { expect } from "earl";

import { withDocumentOpenedByTestCoqLsp } from "../../coqLsp/coqLspBuilders";

import { CoqProofChecker } from "../../core/coqProofChecker";
import { ProofCheckResult } from "../../core/coqProofChecker";

import { Uri } from "../../utils/uri";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

suite("`CoqProofChecker` tests", () => {
    async function checkProofsForAdmitsFromFile(
        resourcePath: string[],
        positions: { line: number; character: number }[],
        proofsToCheck: string[][],
        projectRootPath?: string[]
    ): Promise<ProofCheckResult[][]> {
        const [filePath, rootDir] = resolveResourcesDir(
            resourcePath,
            projectRootPath
        );
        const fileUri = Uri.fromPath(filePath);
        const documentVersion = 1;

        return withDocumentOpenedByTestCoqLsp(
            { uri: fileUri, version: documentVersion },
            { workspaceRootPath: rootDir },
            (coqLspClient) => {
                const coqProofChecker = new CoqProofChecker(coqLspClient);
                const preparedProofs = proofsToCheck.map((proofs) =>
                    proofs.map(prepareProofBeforeCheck)
                );
                return Promise.all(
                    positions.map(async (position, i) => {
                        const proofCheckRes = await coqProofChecker.checkProofs(
                            fileUri,
                            documentVersion,
                            position,
                            preparedProofs[i]
                        );
                        return proofCheckRes.map((res) => {
                            return {
                                ...res,
                                proof: unpackProof(res.proof),
                            };
                        });
                    })
                );
            }
        );
    }

    function prepareProofBeforeCheck(proof: string) {
        return ` { ${proof} }`;
    }

    function unpackProof(text: string): string {
        const flatProof = text.replace(/\n/g, " ");
        return flatProof
            .trim()
            .slice(1, flatProof.length - 2)
            .trim();
    }

    test("Check simple admits", async () => {
        const filePath = ["small_document.v"];
        const proofs = [["reflexivity.", "auto."]];
        const positions = [{ line: 9, character: 4 }];

        const results = await checkProofsForAdmitsFromFile(
            filePath,
            positions,
            proofs
        );

        const expected: ProofCheckResult[] = [
            {
                proof: "reflexivity.",
                isValid: false,
                diagnostic:
                    'In environment\nn : nat\nUnable to unify "n" with\n "0 + n + 0".',
            },
            {
                proof: "auto.",
                isValid: true,
                diagnostic: undefined,
            },
        ];

        expect(results).toHaveLength(1);
        for (const [i, result] of results[0].entries()) {
            expect(result).toEqual(expected[i]);
        }
    });

    test("Check proof check for many admits", async () => {
        const filePath = ["test_many_admits.v"];
        const proofs = [
            ["auto."],
            ["intros.", "assumption."],
            ["intros.", "left. reflexivity."],
            ["kek.", "right. auto."],
            ["reflexivity."],
            ["lol."],
        ];

        const positions = [
            { line: 2, character: 4 },
            { line: 8, character: 4 },
            { line: 16, character: 8 },
            { line: 19, character: 8 },
            { line: 26, character: 4 },
            { line: 32, character: 4 },
        ];

        const expected: ProofCheckResult[][] = [
            [
                {
                    proof: "auto.",
                    isValid: true,
                    diagnostic: undefined,
                },
            ],
            [
                {
                    proof: "intros.",
                    isValid: false,
                    diagnostic:
                        "This proof is focused, but cannot be unfocused this way",
                },
                {
                    proof: "assumption.",
                    isValid: true,
                    diagnostic: undefined,
                },
            ],
            [
                {
                    proof: "intros.",
                    isValid: false,
                    diagnostic:
                        "This proof is focused, but cannot be unfocused this way",
                },
                {
                    proof: "left. reflexivity.",
                    isValid: true,
                    diagnostic: undefined,
                },
            ],
            [
                {
                    proof: "kek.",
                    isValid: false,
                    diagnostic:
                        "The reference kek was not found in the current\nenvironment.",
                },
                {
                    proof: "right. auto.",
                    isValid: true,
                    diagnostic: undefined,
                },
            ],
            [
                {
                    proof: "reflexivity.",
                    isValid: true,
                    diagnostic: undefined,
                },
            ],
            [
                {
                    proof: "lol.",
                    isValid: false,
                    diagnostic:
                        "The reference lol was not found in the current\nenvironment.",
                },
            ],
        ];

        const results = await checkProofsForAdmitsFromFile(
            filePath,
            positions,
            proofs
        );

        expect(results).toHaveLength(6);
        for (const [i, result] of results.entries()) {
            expect(result).toHaveLength(expected[i].length);
            for (const [j, res] of result.entries()) {
                expect(res).toEqual(expected[i][j]);
            }
        }
    }).timeout(10000);
});
