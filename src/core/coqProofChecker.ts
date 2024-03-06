import { Mutex } from "async-mutex";
import { appendFileSync, existsSync, unlinkSync, writeFileSync } from "fs";
import * as path from "path";
import { Position } from "vscode-languageclient";

import { CoqLspClient } from "../coqLsp/coqLspClient";

import { Uri } from "../utils/uri";

export type ProofCheckResult = [string, boolean, string | null];
type Proof = string;

export interface CoqProofCheckerInterface {
    checkProofs(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        proofs: Proof[]
    ): Promise<[string, boolean, string | null][]>;
}

export class CoqLspTimeoutError extends Error {
    constructor(message: string) {
        super(message);
        this.name = "CoqLspTimeoutError";
    }
}

export class CoqProofChecker implements CoqProofCheckerInterface {
    private mutex: Mutex = new Mutex();

    constructor(private coqLspClient: CoqLspClient) {}

    async checkProofs(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        proofs: Proof[],
        coqLspTimeoutMillis: number = 60000
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

    private makeAuxFileName(
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
        const auxFileUri = this.makeAuxFileName(
            sourceDirPath,
            prefixEndPosition
        );
        const sourceFileContent = sourceFileContentPrefix.join("\n");
        writeFileSync(auxFileUri.fsPath, sourceFileContent);

        const results: ProofCheckResult[] = [];
        try {
            // 2. Issue open text document request
            await this.coqLspClient.openTextDocument(auxFileUri);
            let auxFileVersion = 1;

            // 3. Iterate over the proofs and issue getFirstGoalAtPoint request with
            // pretac = proof
            for (const proof of proofs) {
                // 3.1. Check if the proof contains admit
                if (this.checkIfProofContainsAdmit(proof)) {
                    results.push([proof, false, "Proof contains admit"]);
                    continue;
                }

                auxFileVersion += 1;
                // 4. Append the proof the end of the aux file
                appendFileSync(auxFileUri.fsPath, proof);

                // 5. Issue update text request
                const diagnosticMessage =
                    await this.coqLspClient.updateTextDocument(
                        sourceFileContentPrefix,
                        proof,
                        auxFileUri,
                        auxFileVersion
                    );

                // 6. Check diagnostics
                results.push([
                    proof,
                    diagnosticMessage === undefined,
                    diagnosticMessage ?? null,
                ]);

                // 7. Bring file to the previous state
                writeFileSync(auxFileUri.fsPath, sourceFileContent);
            }
        } finally {
            // 4. Issue close text document request
            await this.coqLspClient.closeTextDocument(auxFileUri);

            // 5. Remove the aux file
            unlinkSync(auxFileUri.fsPath);
        }

        return results;
    }
}

const forbiddenAdmitTactics = ["admit.", "Admitted.", "Abort."];
