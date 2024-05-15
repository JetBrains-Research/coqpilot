import { expect } from "earl";

import {
    CheckCoqCommand,
    PrintCoqCommand,
    SearchCoqCommand,
} from "../../agentServer/services/coqCommandType";

suite("AgentServer: Check validation rules for Search Coq Command", () => {
    test("Valid pattern", () => {
        const command = new SearchCoqCommand("pattern");
        expect(command.get().ok).toEqual(true);
        expect(command.get().val).toEqual("Search (pattern).");
    });

    test("Empty pattern", () => {
        const command = new SearchCoqCommand("");
        expect(command.get().val).toBeA(Error);
    });

    test("Pattern with new line", () => {
        const command = new SearchCoqCommand("pat\ntern");
        expect(command.get().val).toBeA(Error);
    });

    test("Pattern with quotes", () => {
        const command = new SearchCoqCommand('pat"tern');
        expect(command.get().val).toBeA(Error);
    });
});

suite("AgentServer: Check validation rules for Print Coq Command", () => {
    test("Valid term", () => {
        const command = new PrintCoqCommand("term");
        expect(command.get().ok).toEqual(true);
        expect(command.get().val).toEqual("Print term.");
    });

    test("Empty term", () => {
        const command = new PrintCoqCommand("");
        expect(command.get().val).toBeA(Error);
    });

    test("Term with new line", () => {
        const command = new PrintCoqCommand("ter\nm");
        expect(command.get().val).toBeA(Error);
    });

    test("Term with dots", () => {
        const command = new PrintCoqCommand("ter.m");
        expect(command.get().val).toBeA(Error);
    });
});

suite("AgentServer: Check validation rules for Check Coq Command", () => {
    test("Valid term", () => {
        const command = new CheckCoqCommand("term");
        expect(command.get().ok).toEqual(true);
        expect(command.get().val).toEqual("Check term.");
    });

    test("Empty term", () => {
        const command = new CheckCoqCommand("");
        expect(command.get().val).toBeA(Error);
    });

    test("Term with new line", () => {
        const command = new CheckCoqCommand("ter\nm");
        expect(command.get().val).toBeA(Error);
    });

    test("Term with dots", () => {
        const command = new CheckCoqCommand("ter.m");
        expect(command.get().val).toBeA(Error);
    });
});
