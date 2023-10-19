import { 
    ProofView,
} from '../../coqLspClient/proofView';

import {
    Range,
    Position
} from "vscode-languageserver-types";

import {
    readFileSync, 
    unlinkSync,
    writeFileSync
} from 'fs';

import { 
    workspace, 
    Position as VPosition, 
    Uri, 
    window
} from 'vscode';

import { CoqLspClient } from '../../coqLspClient/coqLspClient';
import { StatusBarButton } from '../../editor/enableButton';
import * as path from 'path';
import * as assert from 'assert';
import { makeAuxfname } from '../../coqLspClient/utils';
import * as common from '../common';

suite('ProofView auxTheorem tests', () => {
    const statusItem = new StatusBarButton();
    const wsConfig = workspace.getConfiguration("coqpilot");
    const dirname = path.dirname(path.dirname(path.dirname(__dirname)));

    interface TestData {
        fileRoot: string,
        filePath: string,
        positions: Position[],
        goals: string[],
    }

    const testData: TestData[] = [
        {
            fileRoot: path.join(dirname, 'src', 'test', 'resources', 'coqProj'),
            filePath: path.join(dirname, 'src', 'test', 'resources', 'coqProj', 'theories', 'B.v'),
            positions: [
                new VPosition(4, 0),
                new VPosition(4, 14),
                new VPosition(4, 21)
            ],
            goals: [
                "Lemma test_aux_thr  :\n   forall n : nat, evenb (S n) = negb (evenb n).", 
                "Lemma test_aux_thr (n : nat) :\n   evenb (S n) = negb (evenb n).", 
                "Lemma test_aux_thr (n : nat) :\n   negb (evenb n) = negb (evenb n)."
            ]
        }, 
        {
            fileRoot: undefined, 
            filePath: path.join(dirname, 'src', 'test', 'resources', 'integration_test.v'),
            positions: [
                new VPosition(2, 4),
                new VPosition(3, 4),
                new VPosition(8, 13)
            ],
            goals: [
                "Lemma test_thr_aux_thr  :\n   forall n : nat, 0 + n = n.", 
                "Lemma test_thr_aux_thr (n : nat) :\n   0 + n = n.", 
                "Lemma test_thr1_aux_thr (n : nat) :\n   0 + n + 0 = n."
            ]
        }, 
        {
            fileRoot: undefined, 
            filePath: path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v'),
            positions: [
                new VPosition(1, 4),
                new VPosition(4, 4),
                new VPosition(7, 4)
            ],
            goals: [
                "Lemma test_aux_thr  :\n   True.", 
                "Lemma test2_aux_thr  :\n   False.", 
                "Lemma test3_aux_thr  :\n   1 = 1."
            ]
        }
    ];

	test('Check get aux theorem', async () => {
        for (const data of testData) {
            const { fileRoot, filePath, positions, goals } = data;
            const text = readFileSync(filePath, 'utf8');
            const uri = Uri.file(filePath);
            const auxFile = makeAuxfname(uri);
            const rootUri = fileRoot ? Uri.file(fileRoot) : undefined;

            const client = new CoqLspClient(statusItem, wsConfig, rootUri);
            await client.start();
            const proofView = new ProofView(client, statusItem); 

            for (let i = 0; i < goals.length; i++) {
                const auxThr = await proofView.getAuxTheoremAtCurPosition(
                    auxFile, text, positions[i]
                );

                assert.ok(auxThr);
                const [thrStatement, _] = auxThr;
                assert.strictEqual(thrStatement, goals[i]);
            }

            unlinkSync(auxFile.fsPath);
            client.stop();
        }
    }).timeout(5000);
});


suite('ProofView checkTheorems tests', () => {
    const statusItem = new StatusBarButton();
    const wsConfig = workspace.getConfiguration("coqpilot");
    const dirname = path.dirname(path.dirname(path.dirname(__dirname)));

    interface TestData {
        context: string, 
        filePath: string,
        proofs: string[],
        verdicts: [boolean, string][]
    }

    const testData: TestData[] = [
        {
            context: "Theorem plus_O_n'' : forall n:nat, 0 + n = n.\n",
            filePath: path.join(dirname, 'src', 'test', 'resources', 'aux.v'),
            proofs: [
                "Proof. intros n. Qed.",
                "Proof. kek. Qed.",
                "Proof. lol. Qed.",
                "Proof. assumption. Qed.",
                "Proof. Admitted.",
                "Proof. reflexivity. Abort.",
                "Proof. reflexivity. Qed.",
                "Proof. auto. Qed.",
            ], 
            verdicts: [
                [false, " (in proof plus_O_n''): Attempt to save an incomplete proof"],
                [false, "The reference kek was not found in the current"],
                [false, "The reference lol was not found in the current"],
                [false, "No such assumption."],
                [false, "Proof contains 'Abort.' or 'Admitted.'"],
                [false, "Proof contains 'Abort.' or 'Admitted.'"],
                [true, null]
            ]
        }, 
        {
            context: "Theorem test_thr1 : forall n:nat, 0 + n + 0 = n.\n", 
            filePath: path.join(dirname, 'src', 'test', 'resources', 'aux.v'),
            proofs: [
                "Proof.\n```coq Incorrect proof```\nQed.",
                "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nsimpl.\nPrint plus.\nrewrite plus_0_r.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nrewrite plus_0_r.\nrewrite plus_0_l.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nrewrite <- plus_n_O.\nrewrite <- plus_n_O at 1.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nsimpl.\nrewrite plus_0_r.\nreflexivity.\nQed.",
                "Proof.\nintros n.\nPrint plus.\nsimpl.\nrewrite <- plus_n_O.\nreflexivity.\nQed."
            ],
            verdicts: [
                [false, "The reference coq was not found in the current"],
                [false, "The variable plus_0_r was not found in the current"],
                [false, "The variable plus_0_r was not found in the current"],
                [false, "The variable plus_0_r was not found in the current"],
                [false, "The variable plus_0_r was not found in the current"],
                [false, 'Found no subterm matching "?n + 0" in the current goal.'],
                [false, "The variable plus_0_r was not found in the current"],
                [true, null]
            ]
        }
    ];

	test('Test check proofs', async () => {
        for (const data of testData) {
            const { context, filePath, proofs, verdicts } = data;
            writeFileSync(filePath, context);

            const client = new CoqLspClient(statusItem, wsConfig);
            await client.start();
            const proofView = new ProofView(client, statusItem); 
            await proofView.openFile(Uri.file(filePath));
            const res = await proofView.checkTheorems(Uri.file(filePath), proofs);

            assert.strictEqual(res.length, verdicts.length);
            for (let i = 0; i < res.length; i++) {
                assert.strictEqual(res[i][0], verdicts[i][0]);
                assert.strictEqual(res[i][1], verdicts[i][1]);
            }

            client.stop();
        }
    }).timeout(5000);
});

suite('ProofView parseFile tests', () => {
    const statusItem = new StatusBarButton();
    const wsConfig = workspace.getConfiguration("coqpilot");
    const dirname = path.dirname(path.dirname(path.dirname(__dirname)));

    interface TheoremData {
        statementRange: Range, 
        name: string,
        numOfSteps: number,
        isIncomplete: boolean,
        endPos: Position, 
        proof: string
    }

    interface TestData {
        fileRoot: string,
        filePath: string,
        theorems: TheoremData[]
    }

    const testData: TestData[] = [
        {
            fileRoot: path.join(dirname, 'src', 'test', 'resources', 'coqProj'),
            filePath: path.join(dirname, 'src', 'test', 'resources', 'coqProj', 'theories', 'B.v'),
            theorems: [
                {
                    statementRange: { start: { line: 2, character: 0 }, end: { line: 2, character: 60 } },
                    name: "test",
                    numOfSteps: 5,
                    isIncomplete: false,
                    endPos: { line: 5, character: 4 },
                    proof: "Proof.\nintros n.\nsimpl.\nreflexivity.\nQed.\n"
                }
            ]
        },
        {
            fileRoot: undefined,
            filePath: path.join(dirname, 'src', 'test', 'resources', 'integration_test.v'),
            theorems: [
                {
                    statementRange: { start: { line: 0, character: 0 }, end: { line: 0, character: 43 } },
                    name: "test_thr",
                    numOfSteps: 5,
                    isIncomplete: false,
                    endPos: { line: 4, character: 4 },
                    proof: "Proof.\nintros n.\nPrint plus.\nreflexivity.\nQed.\n"
                },
                {
                    statementRange: { start: { line: 6, character: 0 }, end: { line: 6, character: 46 } },
                    name: "test_thr1",
                    numOfSteps: 6,
                    isIncomplete: false,
                    endPos: { line: 11, character: 4 },
                    proof: "Proof.\nintros n.\nPrint plus.\nrewrite <- plus_n_O.\nreflexivity.\nQed.\n"
                }
            ]
        },
        {
            fileRoot: undefined,
            filePath: path.join(dirname, 'src', 'test', 'resources', 'interaction_test_1.v'),
            theorems: [
                {
                    statementRange: { start: { line: 0, character: 0 }, end: { line: 0, character: 19 } },
                    name: "test",
                    numOfSteps: 1,
                    isIncomplete: true,
                    endPos: { line: 1, character: 9 },
                    proof: "Admitted.\n"
                },
                {
                    statementRange: { start: { line: 3, character: 0 }, end: { line: 3, character: 21 } },
                    name: "test2",
                    numOfSteps: 1,
                    isIncomplete: true,
                    endPos: { line: 4, character: 9 },
                    proof: "Admitted.\n"
                },
                {
                    statementRange: { start: { line: 6, character: 0 }, end: { line: 6, character: 21 } },
                    name: "test3",
                    numOfSteps: 1,
                    isIncomplete: true,
                    endPos: { line: 7, character: 9 },
                    proof: "Admitted.\n"
                }
            ]
        }
    ];

    const rangesEqual = (r1: Range, r2: Range): boolean => {
        return r1.start.line === r2.start.line && r1.start.character === r2.start.character &&
            r1.end.line === r2.end.line && r1.end.character === r2.end.character;
    };

	test('Test check proofs', async () => {
        for (const data of testData) {
            const { fileRoot, filePath, theorems } = data;
            const uri = Uri.file(filePath);
            const rootUri = fileRoot ? Uri.file(fileRoot) : undefined;
            await common.openTextFile(uri);

            const client = new CoqLspClient(statusItem, wsConfig, rootUri);
            await client.start();
            const proofView = new ProofView(client, statusItem); 

            const res = await proofView.parseFile(window.activeTextEditor);
    
            assert.strictEqual(res.length, theorems.length);
            for (let i = 0; i < res.length; i++) {
                const theorem = theorems[i];
                const thrRes = res[i];

                assert.strictEqual(thrRes.name, theorem.name);
                assert.strictEqual(thrRes.proof.proof_steps.length, theorem.numOfSteps);
                assert.strictEqual(thrRes.proof.is_incomplete, theorem.isIncomplete);
                assert.strictEqual(thrRes.proof.end_pos.end.line, theorem.endPos.line);
                assert.strictEqual(thrRes.proof.end_pos.end.character, theorem.endPos.character);
                assert.strictEqual(thrRes.proof.onlyText(), theorem.proof);
                assert.ok(rangesEqual(thrRes.statement_range, theorem.statementRange));
            }

            client.stop();
        }
    }).timeout(5000);
});