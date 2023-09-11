import { LlmPromptInterface } from './llmPromptInterface';
import { LLMInterface } from './llmInterface';
import { EvaluationLogger } from './evaluationLogger';
import { coqlspmodels } from 'coqlsp-client';

export class Interactor {
    llmPrompt: LlmPromptInterface;
    llmInterface: LLMInterface;
    logAttemps: boolean;
    logFilePath: string | null;
    contents: string[] | null;
    contentsPointer: number;
    timeout: number;
    runLogger: EvaluationLogger;
    shots: number;

    constructor(
        llmPrompt: LlmPromptInterface, 
        llmInterface: LLMInterface, 
        logAttemps: boolean = false, 
        shots: number = 1
    ) {
        this.llmPrompt = llmPrompt;
        this.llmInterface = llmInterface;
        this.logAttemps = logAttemps;

        this.llmInterface.initHistory(this.llmPrompt);
        this.logFilePath = null;
        this.contents = null;
        this.contentsPointer = 0;
        this.timeout = 20;
        this.shots = shots;

        this.runLogger = new EvaluationLogger(
            this.llmPrompt.coqFile,
            this.llmPrompt.promptStrategy,
            shots, 
            this.llmPrompt.statementsToRanges, 
            logAttemps
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
     * @param shots The number of attempts to find a proof.
     * @returns The correct proof or undefined if no proof was found.
     */
    async runProofGeneration(theoremName: string): Promise<string | undefined> {
        const theoremStatement = this.llmPrompt.getTheoremStatementByName(theoremName);
        this.runLogger.onStartLlmResponseFetch(theoremName);

        let llmResponse = await this.llmInterface.sendMessageWithoutHistoryChange(
            theoremStatement,
            this.shots
        );

        this.runLogger.onEndLlmResponseFetch();
        this.runLogger.onTheoremProofStart();

        let verifyProofsAttempts = 1;
        let proofCheckResult: [boolean, string][] = [];

        while(verifyProofsAttempts > 0) {
            try {
                proofCheckResult = await this.llmPrompt.verifyProofs(theoremStatement, llmResponse);
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
                this.runLogger.onEndLlmResponseFetch();
                
                if (e instanceof coqlspmodels.ProofViewError) {
                    this.runLogger.onAttemptException(0, theoremName, `ProofViewError: ${e.message}`);
                } else {
                    this.runLogger.onAttemptException(0, theoremName, e.message);
                    this.llmPrompt.restartProofView();
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

        this.runLogger.onTheoremProofEnd(theoremStatement, this.llmPrompt.correctProofs[theoremStatement]);

        if (foundProof) {
            return foundProof;
        } 

        return undefined;
    }

    stop() {
        this.runLogger.onEvaluationFinish();
        this.llmPrompt.stop();
    }
}