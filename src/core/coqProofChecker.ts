import { Mutex } from "async-mutex";
import { Position } from "vscode-languageclient";

import { CoqLspClient } from "../coqLsp/coqLspClient";
import { CoqLspTimeoutError } from "../coqLsp/coqLspTypes";

import { Uri } from "../utils/uri";
import { EventLogger } from "../logging/eventLogger";

export interface ProofCheckResult {
    proof: string;
    isValid: boolean;
    diagnostic?: string;
}

type Proof = string;

export class CoqProofChecker {
    private mutex: Mutex = new Mutex();

    constructor(private coqLspClient: CoqLspClient, private eventLogger?: EventLogger) {}

    async checkProofs(
        fileUri: Uri,
        documentVersion: number,
        positionToCheckAt: Position,
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
                    positionToCheckAt,
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
        positionToCheckAt: Position,
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

            const goalsResult = await this.coqLspClient.getGoalsAtPoint(
                positionToCheckAt,
                fileUri,
                documentVersion,
                proof
            );

            if (goalsResult.err) {
                this.eventLogger?.log(
                    'new-proof-check',
                    `Checking proog: ${proof}, goalsResult: ${goalsResult.val.message}`
                );
            }

            results.push({
                proof: proof,
                isValid: goalsResult.ok,
                diagnostic: goalsResult.err
                    ? goalsResult.val.message
                    : undefined,
            });
        }

        return results;
    }

    dispose(): void {
        this.coqLspClient.dispose();
    }
}

const forbiddenAdmitTactics = ["admit.", "Admitted.", "Abort."];
