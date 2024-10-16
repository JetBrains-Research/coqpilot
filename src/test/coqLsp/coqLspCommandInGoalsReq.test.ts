import { expect } from "earl";
import { Result } from "ts-results";

import { createTestCoqLspClient } from "../../coqLsp/coqLspBuilders";
import { Goal, PpString } from "../../coqLsp/coqLspTypes";

import { Uri } from "../../utils/uri";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

suite("Request goals with `command/pretac` argument", () => {
    async function getGoalAtPosition(
        position: { line: number; character: number },
        resourcePath: string[],
        command: string,
        projectRootPath?: string[]
    ): Promise<Result<Goal<PpString>[], Error>> {
        const [filePath, rootDir] = resolveResourcesDir(
            resourcePath,
            projectRootPath
        );
        const fileUri = Uri.fromPath(filePath);

        const client = await createTestCoqLspClient(rootDir);
        await client.openTextDocument(fileUri);
        const goals = await client.getGoalsAtPoint(
            position,
            fileUri,
            1,
            command
        );
        await client.closeTextDocument(fileUri);
        client.dispose();

        return goals;
    }

    test("One Coq sentence: fail to solve with bad goal", async () => {
        const goal = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["small_document.v"],
            "reflexivity."
        );

        expect(goal.err).toEqual(true);
        expect(goal.val).toBeA(Error);
        if (goal.val instanceof Error) {
            expect(goal.val.message).toEqual(
                'In environment\nn : nat\nUnable to unify "n" with\n "0 + n + 0".'
            );
        }
    });

    test("One Coq sentence: fail to solve with bad tactic", async () => {
        const goal = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["small_document.v"],
            "reflexivit."
        );

        expect(goal.err).toEqual(true);
        expect(goal.val).toBeA(Error);
        if (goal.err) {
            expect(goal.val.message).toEqual(
                "The reference reflexivit was not found in the current\nenvironment."
            );
        }
    });

    test("One Coq sentence: successfully solve no goals left", async () => {
        const goals = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["small_document.v"],
            "auto."
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("One Coq sentence: successfully solve 1 goal left", async () => {
        const goals = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["test_many_subgoals.v"],
            "auto."
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toHaveLength(1);
            expect(goals.val[0].ty).toEqual("S n + 0 = S n");
        }
    });

    test("One Coq sentence: successfully solve 2 goals left", async () => {
        const goals = await getGoalAtPosition(
            { line: 22, character: 4 },
            ["test_many_subgoals.v"],
            "auto."
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toHaveLength(2);
            expect(goals.val[0].ty).toEqual(
                "Second = First \\/ Second = Second \\/ Second = Third"
            );
            expect(goals.val[1].ty).toEqual(
                "Third = First \\/ Third = Second \\/ Third = Third"
            );
        }
    });

    test("One Coq sentence wrapped into curly braces: solve successfully", async () => {
        const goals = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["small_document.v"],
            " { auto. }"
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("One Coq sentence wrapped into curly braces: bad proof", async () => {
        const goals = await getGoalAtPosition(
            { line: 9, character: 4 },
            ["small_document.v"],
            " { kek. }"
        );

        expect(goals.err).toEqual(true);
        if (goals.err) {
            expect(goals.val.message).toEqual(
                "The reference kek was not found in the current\nenvironment."
            );
        }
    });

    test("One Coq sentence wrapped into curly braces: good proof, test indent", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ auto. }"
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("Many Coq sentences: good proof", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "simpl. induction n. reflexivity. auto."
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("Many Coq sentences: bad proof", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "simpl. induction n. reflexivity. reflexivity."
        );

        expect(goals.err).toEqual(true);
        if (goals.err) {
            expect(goals.val.message).toEqual(
                'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
            );
        }
    });

    test("Many Coq sentences: good proof with multiple curly braces", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ simpl. \n      induction n. \n      { reflexivity. }\n      auto. \n    }"
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("Many Coq sentences: bad proof with multiple curly braces", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ simpl. \n      induction n. \n      { reflexivity. }\n      reflexivity. \n    }"
        );

        expect(goals.err).toEqual(true);
        if (goals.err) {
            expect(goals.val.message).toEqual(
                'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
            );
        }
    });

    test("Many Coq sentences: good proof with bullets", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ \n        simpl. \n        induction n. \n        - reflexivity.\n        - auto. \n    }"
        );

        expect(goals.ok).toEqual(true);
        if (goals.ok) {
            expect(goals.val).toBeEmpty();
        }
    });

    test("Many Coq sentences: bad proof with bullets", async () => {
        const goals = await getGoalAtPosition(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ \n        simpl. \n        induction n. \n        - reflexivity.\n        - reflexivity. \n    }"
        );

        expect(goals.err).toEqual(true);
        if (goals.err) {
            expect(goals.val.message).toEqual(
                'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
            );
        }
    });
});
