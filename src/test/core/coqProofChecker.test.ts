import * as path from "path";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { expect } from "earl";
import { getResourceFolder, createCoqLspClient } from "../commonTestFunctions";
import { ProofCheckResult } from "../../core/coqProofChecker";
import { readFileSync } from "fs";

suite("Coq Proof Checker tests", () => {
    async function checkProofsForAdmitsFromFile(
        resourcePath: string[],
        positions: { line: number; character: number }[],
        proofsToCheck: string[][],
        projectRootPath?: string[]
    ): Promise<ProofCheckResult[][]> {
        const filePath = path.join(getResourceFolder(), ...resourcePath);
        const fileDir = path.dirname(filePath);
        const rootDir = path.join(
            getResourceFolder(),
            ...(projectRootPath ?? [])
        );

        const fileLines = readFileSync(filePath).toString().split("\n");
        const client = createCoqLspClient(rootDir);
        const coqProofChecker = new CoqProofChecker(client);
        const preparedProofs = proofsToCheck.map((proofs) =>
            proofs.map(prepareProofBeforeCheck)
        );

        return Promise.all(
            positions.map(async (position, i) => {
                const textPrefix = getTextBeforePosition(fileLines, position);
                const proofCheckRes = await coqProofChecker.checkProofs(
                    fileDir,
                    textPrefix,
                    position,
                    preparedProofs[i]
                );
                return proofCheckRes.map((res) => {
                    return [unpackProof(res[0]), res[1], res[2]];
                });
            })
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

    function getTextBeforePosition(
        textLines: string[],
        position: { line: number; character: number }
    ): string[] {
        const textPrefix = textLines.slice(0, position.line + 1);
        textPrefix[position.line] = textPrefix[position.line].slice(
            0,
            position.character
        );
        return textPrefix;
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
            ["reflexivity.", false, "In environment"],
            ["auto.", true, null],
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
            [["auto.", true, null]],
            [
                [
                    "intros.",
                    false,
                    "This proof is focused, but cannot be unfocused this way",
                ],
                ["assumption.", true, null],
            ],
            [
                [
                    "intros.",
                    false,
                    "This proof is focused, but cannot be unfocused this way",
                ],
                ["left. reflexivity.", true, null],
            ],
            [
                [
                    "kek.",
                    false,
                    "The reference kek was not found in the current",
                ],
                ["right. auto.", true, null],
            ],
            [["reflexivity.", true, null]],
            [["lol.", false, "The reference lol was not found in the current"]],
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
    }).timeout(5000);
});
