import { Mutex } from "async-mutex";
import { existsSync, unlinkSync, writeFileSync } from "fs";
import * as path from "path";
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
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        proofs: Proof[]
    ): Promise<ProofCheckResult[]>;

    dispose(): void;
}

export class CoqProofChecker implements CoqProofCheckerInterface {
    private mutex: Mutex = new Mutex();

    constructor(private coqLspClient: CoqLspClientInterface) {}

    async checkProofs(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
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
                    sourceDirPath,
                    sourceFileContentPrefix,
                    prefixEndPosition,
                    proofs
                ),
                timeoutPromise,
            ]);
        });
    }

    private buildAuxFileUri(
        sourceDirPath: string,
        holePosition: Position,
        unique: boolean = true
    ): Uri {
        const holeIdentifier = `${holePosition.line}_${holePosition.character}`;
        const defaultAuxFileName = `hole_${holeIdentifier}_cp_aux.v`;
        let auxFilePath = path.join(sourceDirPath, defaultAuxFileName);
        if (unique && existsSync(auxFilePath)) {
            const randomSuffix = Math.floor(Math.random() * 1000000);
            auxFilePath = auxFilePath.replace(
                /\_cp_aux.v$/,
                `_${randomSuffix}_cp_aux.v`
            );
        }

        return Uri.fromPath(auxFilePath);
    }

    private checkIfProofContainsAdmit(proof: Proof): boolean {
        return forbiddenAdmitTactics.some((tactic) => proof.includes(tactic));
    }

    private async checkProofsUnsafe(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        proofs: Proof[]
    ): Promise<ProofCheckResult[]> {
        // 1. Write the text to the aux file
        const auxFileUri = this.buildAuxFileUri(
            sourceDirPath,
            prefixEndPosition
        );
        const sourceFileContent = sourceFileContentPrefix.join("\n");
        writeFileSync(auxFileUri.fsPath, sourceFileContent);

        const results: ProofCheckResult[] = [];
        try {
            // 2. Issue open text document request
            await this.coqLspClient.openTextDocument(auxFileUri);

            // 3. Iterate over the proofs and сheck them
            for (const proof of proofs) {
                // 3.1. Check if the proof contains admit
                if (this.checkIfProofContainsAdmit(proof)) {
                    results.push({
                        proof: proof,
                        isValid: false,
                        diagnostic: "Proof contains admit",
                    });
                    continue;
                }

                // 3.2 Check if proof is valid and closes the first goal
                const goalResult = await this.coqLspClient.getGoalsAtPoint(
                    prefixEndPosition,
                    auxFileUri,
                    1,
                    proof
                );

                results.push({
                    proof: proof,
                    isValid: goalResult.ok,
                    diagnostic: goalResult.err
                        ? goalResult.val.message
                        : undefined,
                });
            }
        } finally {
            // 4. Issue close text document request
            await this.coqLspClient.closeTextDocument(auxFileUri);

            // 5. Remove the aux file
            unlinkSync(auxFileUri.fsPath);
        }

        return results;
    }

    dispose(): void {
        this.coqLspClient.dispose();
    }
}

const forbiddenAdmitTactics = ["admit.", "Admitted.", "Abort."];
