import { 
    DocumentUri, 
    Position 
} from "vscode-languageclient";

import { CoqLspClient } from "../coqLsp/coqLspClient"; 
import * as path from "path";

import { 
    existsSync,
    writeFileSync,
    unlinkSync,
} from "fs";
// P.S. mothods from fs 
// accepts fileUri as well as file path

import { Mutex } from "async-mutex";

export type ProofCheckResult = [string, boolean, string | null];
type Proof = string; 

export interface CoqProofCheckerInterface {
    checkProofs(
        sourceDirPath: string,
        sourceFileContentPrefix: string[], 
        prefixEndPosition: Position,
        proofs: Proof[], 
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
            const timeoutPromise = new Promise<ProofCheckResult[]>((_, reject) => {
                setTimeout(() => {
                    reject(new CoqLspTimeoutError(`checkProofs timed out after ${coqLspTimeoutMillis} milliseconds`));
                }, coqLspTimeoutMillis);
            });

            return Promise.race([
                this.checkProofsUnsafe(
                    sourceDirPath, sourceFileContentPrefix, prefixEndPosition, proofs
                ),
                timeoutPromise
            ]);
        });
    }

    private makeAuxFileName(
        sourceDirPath: string, 
        holePosition: Position,
        unique: boolean = true, 
    ): DocumentUri {
        const holeIdentifier = `${holePosition.line}_${holePosition.character}`;
        const defaultAuxFileName = `${holeIdentifier}_cp_aux.v`;
        let auxFilePath = path.join(sourceDirPath, defaultAuxFileName);
        if (unique && existsSync(auxFilePath)) {
            const randomSuffix = Math.floor(Math.random() * 1000000);
            auxFilePath = auxFilePath.replace(/\_cp_aux.v$/, `_${randomSuffix}_cp_aux.v`);
        }
        
        return auxFilePath;
    }

    private async checkProofsUnsafe(
        sourceDirPath: string,
        sourceFileContentPrefix: string[], 
        prefixEndPosition: Position,
        proofs: Proof[], 
    ): Promise<ProofCheckResult[]> {
        // 1. Write the text to the aux file
        const auxFileUri = this.makeAuxFileName(sourceDirPath, prefixEndPosition);
        writeFileSync(auxFileUri, sourceFileContentPrefix.join("\n"));
        
        const results: ProofCheckResult[] = [];
        try {
            // 2. Issue open text document request
            await this.coqLspClient.openTextDocument(auxFileUri);
            let auxFileVersion = 1; 

            // 3. Iterate over the proofs and issue getFirstGoalAtPoint request with 
            // pretac = proof
            for (const proof of proofs) {
                auxFileVersion += 1;
                const goal = await this.coqLspClient.getFirstGoalAtPoint(
                    prefixEndPosition, 
                    auxFileUri, 
                    auxFileVersion, 
                    proof
                );
                console.log("DEBUG: ", goal); 
                results.push([proof, goal instanceof Error, goal instanceof Error ? goal.message : null]);
            }
        } finally {
            // 4. Issue close text document request
            await this.coqLspClient.closeTextDocument(auxFileUri);

            // 5. Remove the aux file
            unlinkSync(auxFileUri);
        }

        return results;
    }
}