import { LLMPrompt } from './llmPromptInterface';
import { LLMInterface } from './llmInterface';
import { EvaluationLogger } from './evaluationLogger';
import { ProgressBar } from '../extension/progressBar';
import { ProofViewError } from '../lib/pvTypes';
import { Uri } from 'vscode';

export class Interactor {
    llmPrompt: LLMPrompt;
    llmInterface: LLMInterface;
    logAttemps: boolean;
    logFilePath: string | null;
    contents: string[] | null;
    contentsPointer: number;
    timeout: number;
    runLogger: EvaluationLogger;
    shots: number;
    progressBar: ProgressBar;

    constructor(
        llmPrompt: LLMPrompt, 
        llmInterface: LLMInterface, 
        progressBar: ProgressBar,
        logAttemps: boolean = false, 
        shots: number = 1,
        logFolderPath: string | null = null
    ) {
        this.llmPrompt = llmPrompt;
        this.llmInterface = llmInterface;
        this.logAttemps = logAttemps;
        this.progressBar = progressBar;

        this.llmInterface.initHistory(this.llmPrompt);
        this.logFilePath = null;
        this.contents = null;
        this.contentsPointer = 0;
        this.timeout = 20;
        this.shots = shots;

        this.runLogger = new EvaluationLogger(
            this.llmPrompt.promptStrategy,
            shots, 
            logAttemps,
            logFolderPath
        );
    }

    /**
     * Retrieves theorems we want to evaluate the LLM on 
     * from the LLMPrompt object, then sends them to the
     * LLMInterface object for evaluation. 
     * Then tries to check the proof returned by the LLM
     * using the LLMPrompt object with the ProofView inside.
     * Returns the ratio of theorems for which the proof has
     * been found successfully to the amount of theorems 
     * provided for evaluation.
     * 
     * @param theoremName The name of the theorem to evaluate.
     * @param theoremStatement The statement of the theorem to evaluate.
     * @param originalName The name of the theorem from which the hole was generated.
     * @returns The correct proof or undefined if no proof was found.
     */
    async runProofGeneration(
        theoremName: string, 
        theoremStatement: string, 
        uri: Uri,
        fnVerifyProofs: (uri: Uri, proofs: string[]) => Promise<[boolean, string | null][]>
    ): Promise<string | undefined> {
        this.runLogger.onStartLlmResponseFetch(theoremName);
        this.progressBar.initialize(100, "id");

        let llmResponse = await this.llmInterface.sendMessageWithoutHistoryChange(
            theoremStatement,
            this.shots
        ).catch((e) => {
            this.runLogger.onException(e.message);
            throw e;
        });
        // Surround with curly braces and remove Proof. and Qed.
        llmResponse = llmResponse.map(this.llmPrompt.thrProofToBullet);

        this.progressBar.finish();
        this.runLogger.onEndLlmResponseFetch();
        this.runLogger.onTheoremProofStart();

        let verifyProofsAttempts = 1;
        let proofCheckResult: [boolean, string][] = [];

        while(verifyProofsAttempts > 0) {
            try {
                proofCheckResult = await fnVerifyProofs(uri, llmResponse);
                break;
            } catch (e) {
                verifyProofsAttempts--;
                if (verifyProofsAttempts === 0) {
                    throw e;
                }

                this.runLogger.onProofCheckFail(e.message);

                this.runLogger.onStartLlmResponseFetch(theoremName);
                llmResponse = await this.llmInterface.sendMessageWithoutHistoryChange(
                    theoremStatement,
                    this.shots
                );
                // Surround with curly braces and remove Proof. and Qed.
                llmResponse = llmResponse.map(this.llmPrompt.thrProofToBullet);
                this.runLogger.onEndLlmResponseFetch();
                
                if (e instanceof ProofViewError) {
                    this.runLogger.onAttemptException(0, theoremName, `ProofViewError: ${e.message}`);
                } else {
                    this.runLogger.onAttemptException(0, theoremName, e.message);
                }
            } 
        }

        let foundProof: string | undefined = undefined;
        for (let i = 0; i < proofCheckResult.length; i++) {
            const [proofStatus, errorMsg] = proofCheckResult[i];
            if (proofStatus) {
                this.runLogger.onSuccessAttempt(
                    i + 1, theoremName, 
                    theoremStatement, llmResponse[i]
                );
                foundProof = llmResponse[i];
            } else {
                this.runLogger.onFailedAttempt(
                    i + 1, theoremName, 
                    theoremStatement, llmResponse[i], errorMsg
                );
            }
        }

        this.runLogger.onTheoremProofEnd(theoremStatement);

        if (foundProof) {
            return this.llmPrompt.cleanFromBrackets(foundProof);
        } 

        return undefined;
    }
}