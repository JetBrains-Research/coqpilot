import { expect } from "earl";

suite("Test Coq code block regexp", () => {
    const coqProofBlockPattern =
        /(Proof(?:\s+using(?:\s+\w+)*)?)\.\s*(.*?)\s*(Qed|Defined|Admitted|Abort)\./s;

    function testCoqProofBlockPattern(code: string, expected: string) {
        const match = code.match(coqProofBlockPattern);
        expect(match).not.toBeNullish();
        expect(match![2]).toEqual(expected);
    }

    test("Simple proof with Proof.", () => {
        const answer = "Proof.intros.\nreflexivity.Qed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof starting with Proof using.", () => {
        const answer = "Proof using.intros.\nreflexivity.Qed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof starting with Proof using. with an argument", () => {
        const answer = "Proof using HW. intros.\nreflexivity.Qed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof starting with Proof using. no space", () => {
        const answer = "Proof using HW.intros.\nreflexivity.Qed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof starting with Proof using. multiple args", () => {
        const answer = "Proof using HW WB HH CH.intros.\nreflexivity.Qed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof ending with Abort.", () => {
        const answer = "Proof using HW WB HH CH.intros.\nreflexivity.Abort.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof ending with Admitted.", () => {
        const answer = "Proof using.intros.\nreflexivity.Admitted.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof ending with Defined.", () => {
        const answer = "Proof using.intros.\nreflexivity.Defined.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });

    test("Proof with multiple Qeds", () => {
        const answer =
            "Proof using.intros.\nreflexivity.Qed. # I wanted to add a comment here\nQed.";
        testCoqProofBlockPattern(answer, "intros.\nreflexivity.");
    });
});
