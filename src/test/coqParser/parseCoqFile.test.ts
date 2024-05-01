import { expect } from "earl";

import { parseTheoremsFromCoqFile } from "../commonTestFunctions/coqFileParser";

suite("Coq file parser tests", () => {
    test("Parse simple small document", async () => {
        const doc = await parseTheoremsFromCoqFile(["small_document.v"]);

        const theoremData = [
            {
                name: "test_thr",
                start: { line: 0, character: 0, offset: 0 },
                end: { line: 4, character: 4, offset: 98 },
                statement: "Theorem test_thr : forall n:nat, 0 + n = n.",
                isIncomplete: false,
                holesStartPoints: [],
            },
            {
                name: "test_thr1",
                start: { line: 6, character: 0, offset: 100 },
                end: { line: 10, character: 9, offset: 200 },
                statement: "Lemma test_thr1 : forall n:nat, 0 + n + 0 = n.",
                isIncomplete: true,
                holesStartPoints: [
                    {
                        start: { line: 9, character: 4, offset: 184 },
                    },
                ],
            },
        ];

        expect(doc).toHaveLength(2);
        for (const [i, theorem] of doc.entries()) {
            expect(theorem.name).toEqual(theoremData[i].name);
            expect(theorem.statement).toEqual(theoremData[i].statement);
            expect(theorem.statement_range.start).toEqual(theoremData[i].start);
            expect(theorem.proof).not.toBeNullish();
            expect(theorem.proof?.end_pos.end).toEqual(theoremData[i].end);
            expect(theorem.proof?.is_incomplete).toEqual(
                theoremData[i].isIncomplete
            );
            expect(theorem.proof!.holes).toHaveLength(
                theoremData[i].holesStartPoints.length
            );
            for (const [j, hole] of theorem.proof!.holes.entries()) {
                expect(hole.range.start).toEqual(
                    theoremData[i].holesStartPoints[j].start
                );
            }
        }
    });

    test("Retreive Multiple nested holes", async () => {
        const doc = await parseTheoremsFromCoqFile(["test_many_admits.v"]);

        const expectedHoleRanges = [
            {
                start: { line: 2, character: 4, offset: 81 },
                end: { line: 2, character: 10, offset: 87 },
            },
            {
                start: { line: 8, character: 4, offset: 201 },
                end: { line: 8, character: 10, offset: 207 },
            },
            {
                start: { line: 16, character: 8, offset: 322 },
                end: { line: 16, character: 14, offset: 328 },
            },
            {
                start: { line: 19, character: 8, offset: 349 },
                end: { line: 19, character: 14, offset: 355 },
            },
            {
                start: { line: 26, character: 4, offset: 454 },
                end: { line: 26, character: 10, offset: 460 },
            },
            {
                start: { line: 32, character: 4, offset: 556 },
                end: { line: 32, character: 10, offset: 562 },
            },
        ];

        const holes = doc.map((theorem) => theorem.proof?.holes ?? []).flat();
        expect(holes).toHaveLength(6);

        for (const [i, hole] of holes.entries()) {
            expect(hole.range).toEqual(expectedHoleRanges[i]);
        }
    });

    test("Test different theorem declarations", async () => {
        const doc = await parseTheoremsFromCoqFile(["test_parse_proof.v"]);

        const theoremData = [
            "test_1",
            "test_2",
            "test_3",
            "test_4",
            "test_6",
            "test_7",
        ];

        const theoremsWithoutProof = doc.filter((theorem) => !theorem.proof);
        const theoremsWithProof = doc.filter((theorem) => theorem.proof);
        const theoremNames = theoremsWithProof.map((theorem) => theorem.name);

        expect(theoremNames).toEqual(theoremData);
        expect(theoremsWithoutProof).toHaveLength(1);
        expect(theoremsWithoutProof[0].name).toEqual("test_5");
    });

    test("Test parse file which is part of project --non-ci", async () => {
        const doc = await parseTheoremsFromCoqFile(
            ["coqProj", "theories", "B.v"],
            ["coqProj"]
        );

        const theoremData = [
            {
                name: "test",
                statement:
                    "Theorem test : forall n : nat, evenb (S n) = negb (evenb n).",
                isIncomplete: false,
            },
        ];

        expect(doc).toHaveLength(theoremData.length);
        for (const [i, theorem] of doc.entries()) {
            expect(theorem.name).toEqual(theoremData[i].name);
            expect(theorem.statement).toEqual(theoremData[i].statement);
            expect(theorem.proof).not.toBeNullish();
            expect(theorem.proof?.is_incomplete).toEqual(
                theoremData[i].isIncomplete
            );
        }
    });
});
