import { Mutex } from "async-mutex";
import { Position } from "vscode-languageclient";

import { CoqLspClientInterface } from "../coqLsp/coqLspClient";
import { CoqLspTimeoutError } from "../coqLsp/coqLspTypes";

import { Uri } from "../utils/uri";

export interface ProofCheckResult {
    proof: string;
    isValid: boolean;
    diagnostic?: string;
}

type Proof = string;

export interface CoqProofCheckerInterface {
    checkProofs(
        fileUri: Uri,
        documentVersion: number,
        checkAtPosition: Position,
        proofs: Proof[],
        coqLspTimeoutMillis?: number
    ): Promise<ProofCheckResult[]>;

    dispose(): void;
}

export class CoqProofChecker implements CoqProofCheckerInterface {
    private mutex: Mutex = new Mutex();

    constructor(private coqLspClient: CoqLspClientInterface) {}

    async checkProofs(
        fileUri: Uri,
        documentVersion: number,
        checkAtPosition: Position,
        proofs: Proof[],
        coqLspTimeoutMillis: number = 15000
    ): Promise<ProofCheckResult[]> {
        return await this.mutex.runExclusive(async () => {
            const timeoutPromise = new Promise<ProofCheckResult[]>(
                (_, reject) => {
                    setTimeout(() => {
                        reject(
                            new CoqLspTimeoutError(
                                `checkProofs timed out after ${coqLspTimeoutMillis} milliseconds`
                            )
                        );
                    }, coqLspTimeoutMillis);
                }
            );

            return Promise.race([
                this.checkProofsUnsafe(
                    fileUri,
                    documentVersion,
                    checkAtPosition,
                    proofs
                ),
                timeoutPromise,
            ]);
        });
    }

    private checkIfProofContainsAdmit(proof: Proof): boolean {
        return forbiddenAdmitTactics.some((tactic) => proof.includes(tactic));
    }

    private async checkProofsUnsafe(
        fileUri: Uri,
        documentVersion: number,
        checkAtPosition: Position,
        proofs: Proof[]
    ): Promise<ProofCheckResult[]> {
        const results: ProofCheckResult[] = [];
        for (const proof of proofs) {
            if (this.checkIfProofContainsAdmit(proof)) {
                results.push({
                    proof: proof,
                    isValid: false,
                    diagnostic: "Proof contains admit",
                });
                continue;
            }

            const goalResult = await this.coqLspClient.getGoalsAtPoint(
                checkAtPosition,
                fileUri,
                documentVersion,
                proof
            );

            results.push({
                proof: proof,
                isValid: goalResult.ok,
                diagnostic: goalResult.err ? goalResult.val.message : undefined,
            });
        }

        return results;
    }

    dispose(): void {
        this.coqLspClient.dispose();
    }
}

const forbiddenAdmitTactics = ["admit.", "Admitted.", "Abort."];
