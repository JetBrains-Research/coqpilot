import { expect } from "earl";
import { Result } from "ts-results";

import { Goal, PpString } from "../../coqLsp/coqLspTypes";

import { Uri } from "../../utils/uri";
import { createCoqLspClient } from "../commonTestFunctions/coqLspBuilder";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

suite("Retrieve goals from Coq file", () => {
    async function getGoalsAtPoints(
        points: { line: number; character: number }[],
        resourcePath: string[],
        projectRootPath?: string[],
        command?: string
    ): Promise<Result<Goal<PpString>, Error>[]> {
        const [filePath, rootDir] = resolveResourcesDir(
            resourcePath,
            projectRootPath
        );
        const fileUri = Uri.fromPath(filePath);

        const client = createCoqLspClient(rootDir);
        await client.openTextDocument(fileUri);
        const goals = await Promise.all(
            points.map(async (point) => {
                return await client.getFirstGoalAtPoint(
                    point,
                    fileUri,
                    1,
                    command
                );
            })
        );
        await client.closeTextDocument(fileUri);

        return goals;
    }

    function unpackGoal(goal: Goal<PpString>): { hyps: string[]; ty: string } {
        return {
            hyps: goal.hyps.map((hyp) => `${hyp.names.join(" ")} : ${hyp.ty}`),
            ty: goal.ty as string,
        };
    }

    test("Small coq file, one request", async () => {
        const goals = await getGoalsAtPoints(
            [{ line: 9, character: 4 }],
            ["small_document.v"]
        );

        const expectedGoal = {
            hyps: ["n : nat"],
            ty: "0 + n + 0 = n",
        };

        expect(goals).toHaveLength(1);
        expect(unpackGoal(goals[0].val as Goal<PpString>)).toEqual(
            expectedGoal
        );
    });

    test("Check correct goals requests", async () => {
        const goals = await getGoalsAtPoints(
            [
                { line: 2, character: 4 },
                { line: 7, character: 19 },
                { line: 16, character: 8 },
                { line: 19, character: 8 },
                { line: 25, character: 14 },
            ],
            ["test_many_admits.v"]
        );

        const expectedGoals = [
            {
                hyps: [],
                ty: "forall (A : Type) (P : A -> Prop) (x : A), P x -> P x",
            },
            {
                hyps: ["A : Type", "P : A -> Prop", "x : A", "H : P x"],
                ty: "P x",
            },
            {
                hyps: [],
                ty: "0 = 0 \\/ 0 <> 0",
            },
            {
                hyps: ["n : nat"],
                ty: "S n = 0 \\/ S n <> 0",
            },
            {
                hyps: ["n : nat"],
                ty: "0 + n = n",
            },
        ];

        expect(goals).toHaveLength(5);
        for (const [i, goal] of goals.entries()) {
            expect(goals[i]).not.toBeA(Error);
            expect(unpackGoal(goal.val as Goal<PpString>)).toEqual(
                expectedGoals[i]
            );
        }
    });

    test("Retreive goal with error", async () => {
        const goals = await getGoalsAtPoints(
            [
                { line: 5, character: 0 },
                { line: 6, character: 0 },
                { line: 9, character: 10 },
                { line: 10, character: 9 },
                { line: 10, character: 3 },
            ],
            ["small_document.v"]
        );

        expect(goals).toHaveLength(5);
        for (const goal of goals) {
            expect(goal).toBeA(Error);
        }
    });

    test("Retreive goal in project with imports", async () => {
        const goals = await getGoalsAtPoints(
            [
                { line: 4, character: 4 },
                { line: 4, character: 14 },
                { line: 4, character: 21 },
            ],
            ["coqProj", "theories", "B.v"],
            ["coqProj"]
        );

        const expectedGoals = [
            {
                hyps: [],
                ty: "forall n : nat, evenb (S n) = negb (evenb n)",
            },
            {
                hyps: ["n : nat"],
                ty: "evenb (S n) = negb (evenb n)",
            },
            {
                hyps: ["n : nat"],
                ty: "negb (evenb n) = negb (evenb n)",
            },
        ];

        expect(goals).toHaveLength(3);
        for (const [i, goal] of goals.entries()) {
            expect(goals[i]).not.toBeA(Error);
            expect(unpackGoal(goal.val as Goal<PpString>)).toEqual(
                expectedGoals[i]
            );
        }
    });
});
