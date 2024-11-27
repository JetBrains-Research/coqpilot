import { expect } from "earl";
import { Result } from "ts-results";

import { withDocumentOpenedByTestCoqLsp } from "../../coqLsp/coqLspBuilders";
import { ProofGoal } from "../../coqLsp/coqLspTypes";

import { Uri } from "../../utils/uri";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

suite("Request goals with `command/pretac` argument", () => {
    async function requestGoalsWithCommandApplied(
        position: { line: number; character: number },
        resourcePath: string[],
        command: string,
        projectRootPath?: string[]
    ): Promise<Result<ProofGoal[], Error>> {
        const [filePath, rootDir] = resolveResourcesDir(
            resourcePath,
            projectRootPath
        );
        const fileUri = Uri.fromPath(filePath);

        return withDocumentOpenedByTestCoqLsp(
            { uri: fileUri },
            { workspaceRootPath: rootDir },
            (coqLspClient) =>
                coqLspClient.getGoalsAtPoint(position, fileUri, 1, command)
        );
    }

    function checkSuccessfullGoalConclusions(
        goals: Result<ProofGoal[], Error>,
        goalConclusions: string[]
    ): void {
        expect(goals.ok).toBeTruthy();
        if (goals.ok) {
            expect(goals.val).toHaveLength(goalConclusions.length);
            for (let i = 0; i < goalConclusions.length; i++) {
                expect(goals.val[i].ty).toEqual(goalConclusions[i]);
            }
        }
    }

    function checkCommandApplicationError(
        goals: Result<ProofGoal[], Error>,
        expectedError: string
    ): void {
        expect(goals.err).toBeTruthy();
        expect(goals.val).toBeA(Error);
        if (goals.err) {
            expect(goals.val.message).toEqual(expectedError);
        }
    }

    test("One Coq sentence: failed to solve with invalid goal", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["small_document.v"],
            "reflexivity."
        );

        checkCommandApplicationError(
            goals,
            'In environment\nn : nat\nUnable to unify "n" with\n "0 + n + 0".'
        );
    });

    test("One Coq sentence: failed to solve with invalid tactic", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["small_document.v"],
            "reflexivit."
        );

        checkCommandApplicationError(
            goals,
            "The reference reflexivit was not found in the current\nenvironment."
        );
    });

    test("One Coq sentence: successfully solved, no goals left", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["small_document.v"],
            "auto."
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("One Coq sentence: successfully solved, 1 goal left", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["test_many_subgoals.v"],
            "auto."
        );

        checkSuccessfullGoalConclusions(goals, ["S n + 0 = S n"]);
    });

    test("One Coq sentence: successfully solved, 2 goals left", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 22, character: 4 },
            ["test_many_subgoals.v"],
            "auto."
        );

        checkSuccessfullGoalConclusions(goals, [
            "Second = First \\/ Second = Second \\/ Second = Third",
            "Third = First \\/ Third = Second \\/ Third = Third",
        ]);
    });

    test("One Coq sentence wrapped into curly braces: solved successfully", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["small_document.v"],
            " { auto. }"
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("One Coq sentence wrapped into curly braces: invalid proof", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 9, character: 4 },
            ["small_document.v"],
            " { kek. }"
        );

        checkCommandApplicationError(
            goals,
            "The reference kek was not found in the current\nenvironment."
        );
    });

    test("One Coq sentence wrapped into curly braces: valid proof, test indent", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ auto. }"
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("Many Coq sentences: valid proof", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "simpl. induction n. reflexivity. auto."
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("Many Coq sentences: invalid proof", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "simpl. induction n. reflexivity. reflexivity."
        );

        checkCommandApplicationError(
            goals,
            'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
        );
    });

    test("Many Coq sentences: valid proof with multiple curly braces", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ simpl. \n      induction n. \n      { reflexivity. }\n      auto. \n    }"
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("Many Coq sentences: invalid proof with multiple curly braces", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ simpl. \n      induction n. \n      { reflexivity. }\n      reflexivity. \n    }"
        );

        checkCommandApplicationError(
            goals,
            'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
        );
    });

    test("Many Coq sentences: valid proof with bullets", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ \n        simpl. \n        induction n. \n        - reflexivity.\n        - auto. \n    }"
        );

        checkSuccessfullGoalConclusions(goals, []);
    });

    test("Many Coq sentences: invalid proof with bullets", async () => {
        const goals = await requestGoalsWithCommandApplied(
            { line: 2, character: 12 },
            ["test_many_subgoals.v"],
            "{ \n        simpl. \n        induction n. \n        - reflexivity.\n        - reflexivity. \n    }"
        );

        checkCommandApplicationError(
            goals,
            'In environment\nn : nat\nIHn : n + 0 = n\nUnable to unify "S n" with\n "S n + 0".'
        );
    });
});
