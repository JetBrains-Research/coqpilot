import { expect } from "earl";

import { CheckCoqCommand } from "../../agentServer/services/coqCommandType";
import { CoqProjectObserverService } from "../../agentServer/services/coqProjectObserverService";

import { serverRunRoot, serverRunRootProj } from "./commonServerTestFunctions";

suite("[AgentServer] CoqProjectObserverService common tests", () => {
    test("Get project root", () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        expect(service.getProjectRoot()).toEqual(serverRunRoot);
    });

    test("Get theorem names from file", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const theoremNames =
            await service.getTheoremNamesFromFile("small_document.v");
        expect(theoremNames).toEqual(["test_thr", "test_thr1"]);
    });

    test("Get theorem names from file: coq project", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRootProj;
        const service = new CoqProjectObserverService();
        const theoremNames =
            await service.getTheoremNamesFromFile("theories/B.v");
        expect(theoremNames).toEqual(["test"]);
    });

    test("Get all Coq files in project", () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const coqFiles = service.getCoqFilesInProject();
        expect(coqFiles).toEqual([
            {
                name: "build_chat_theorems.v",
                pathFromRoot: "build_chat_theorems.v",
            },
            { name: "A.v", pathFromRoot: "coqProj/theories/A.v" },
            { name: "B.v", pathFromRoot: "coqProj/theories/B.v" },
            { name: "C.v", pathFromRoot: "coqProj/theories/C.v" },
            { name: "harder_than_auto.v", pathFromRoot: "harder_than_auto.v" },
            { name: "small_document.v", pathFromRoot: "small_document.v" },
            { name: "test_many_admits.v", pathFromRoot: "test_many_admits.v" },
            { name: "test_parse_proof.v", pathFromRoot: "test_parse_proof.v" },
        ]);
    });
});

suite("[AgentServer] CoqProjectObserverService run Coq Command tests", () => {
    test("Run Check with valid arg", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const result = await service.runCoqCommand(
            "small_document.v",
            new CheckCoqCommand("test_thr")
        );
        expect(result).toEqual(["test_thr\n     : forall n : nat, 0 + n = n"]);
    });

    test("Run Check with invalid arg", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const promise = service.runCoqCommand(
            "small_document.v",
            new CheckCoqCommand("InvalidTheoremName")
        );
        await expect(promise).toBeRejectedWith(
            "The reference InvalidTheoremName was not found in the current\nenvironment."
        );
    });

    test("Run valid Check in project", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRootProj;
        const service = new CoqProjectObserverService();
        const result = await service.runCoqCommand(
            "theories/B.v",
            new CheckCoqCommand("test")
        );

        expect(result).toEqual([
            "test\n     : forall n : nat, evenb (S n) = negb (evenb n)",
        ]);
    });

    test("Run invalid Check in project", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRootProj;
        const service = new CoqProjectObserverService();
        const promise = service.runCoqCommand(
            "theories/B.v",
            new CheckCoqCommand("InvalidTheoremName")
        );

        await expect(promise).toBeRejectedWith(
            "The reference InvalidTheoremName was not found in the current\nenvironment."
        );
    });
});

suite("[AgentServer] CoqProjectObserverService run check proof", () => {
    test("Check complete proof", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const theoremStatement =
            "Theorem one_another_thr : forall n:nat, 0 + n = n.";
        const proof = "Proof.\n  intros.\n  reflexivity.\nQed.";

        const goal = await service.checkCoqProof(
            "small_document.v",
            theoremStatement + "\n" + proof
        );

        expect(goal.val).toBeNullish();
    });

    test("Check incomplete proof with no errors", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const theoremStatement =
            "Theorem one_another_thr : forall n:nat, 0 + n = n.";
        const proof = "Proof.\n  intros.";

        const goal = await service.checkCoqProof(
            "small_document.v",
            theoremStatement + "\n" + proof
        );

        expect(goal.val).not.toBeNullish();
        expect(goal.val).toEqual({
            hypothesis: ["n : nat"],
            conclusion: "0 + n = n",
        });
    });

    test("Check proof with an error", async () => {
        process.env.SERVER_RUN_ROOT = serverRunRoot;
        const service = new CoqProjectObserverService();
        const theoremStatement =
            "Theorem one_another_thr : forall n:nat, 0 + n = n.";
        const proof = "Proof.\n  undefined_tactic.\nQed.";

        const result = await service.checkCoqProof(
            "small_document.v",
            theoremStatement + "\n" + proof
        );

        expect(result.err).toEqual(true);
        expect(result.val).toEqual(
            "The reference undefined_tactic was not found in the current\nenvironment."
        );
    });
});
