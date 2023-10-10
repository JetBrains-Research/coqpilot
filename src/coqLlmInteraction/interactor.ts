import { LLMPrompt } from './llmPromptInterface';
import { LLMInterface } from './llmInterface';
import { EvaluationLogger } from './evaluationLogger';
import { ProgressBar } from '../extension/progressBar';
import { ProofViewError } from '../lib/pvTypes';
import { Uri } from 'vscode';

export enum GenerationStatus {
    success,
    excededTimeout,
    exception, 
    searchFailed
}

export class GenerationResult<T> {
    readonly status: GenerationStatus;
    readonly message: string | null;
    readonly sender: string | null;
    readonly data: T | null;

    constructor(
        status: GenerationStatus, 
        message: string | null, 
        sender: string | null, 
        data: T | null = null
    ) {
        this.status = status;
        this.message = message;
        this.sender = sender;
        this.data = data;
    }

    static success<T>(data: T): GenerationResult<T> {
        return new GenerationResult<T>(GenerationStatus.success, null, null, data);
    }

    static excededTimeout<T>(): GenerationResult<T> {
        return new GenerationResult<T>(GenerationStatus.excededTimeout, "Exceded timeout for proof generation.", null);
    }

    static exception<T>(message: string, sender: string): GenerationResult<T> {
        return new GenerationResult<T>(GenerationStatus.exception, message, sender);
    }

    static searchFailed<T>(): GenerationResult<T> {
        return new GenerationResult<T>(GenerationStatus.searchFailed, "Search failed.", null);
    }

    isSuccessful(): boolean {
        return this.status === GenerationStatus.success;
    }

    couldNotFindProof(): boolean {
        return this.status === GenerationStatus.searchFailed;
    }

    toString(): string {
        switch (this.status) {
            case GenerationStatus.success:
                return `Success: ${this.data}`;
            case GenerationStatus.exception:
                return `Failed in ${this.sender} with ${this.message}`;
            case GenerationStatus.excededTimeout:
                return `Exceded timeout`;
            case GenerationStatus.searchFailed:
                return `Search failed`;
        }
    }

}

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
    ): Promise<GenerationResult<string>> {
        this.runLogger.onStartLlmResponseFetch(theoremName);
        this.progressBar.initialize(100, "id");

        let llmResponse: string[] | Error | null = null;
        
        await this.llmInterface.sendMessageWithoutHistoryChange(
            theoremStatement,
            this.shots
        ).then((response) => {
            console.log("Response received: " + JSON.stringify(response));
            llmResponse = response;
        }).catch((e) => {
            console.log("Error while generation occured: " + e.message);
            this.runLogger.onException(e.message);
            this.progressBar.finish();

            llmResponse = e;
        });
        
        if (llmResponse instanceof Error) {
            return GenerationResult.exception(llmResponse.message, "Open-ai completion request");
        }

        // Surround with curly braces and remove Proof. and Qed.
        llmResponse = llmResponse.map(this.llmPrompt.thrProofToBullet);

        this.progressBar.finish();
        this.runLogger.onEndLlmResponseFetch();
        this.runLogger.onTheoremProofStart();

        let verifyProofsAttempts = 3;
        let proofCheckResult: [boolean, string][] = [];

        while(verifyProofsAttempts > 0) {
            try {
                proofCheckResult = await fnVerifyProofs(uri, llmResponse);
                break;
            } catch (e) {
                verifyProofsAttempts--;
                if (verifyProofsAttempts === 0) {
                    this.runLogger.onException(e.message);
                    return GenerationResult.exception(e.message, "Coq-lsp error");
                }

                this.runLogger.onProofCheckFail(e.message);

                this.runLogger.onStartLlmResponseFetch(theoremName);
                await this.llmInterface.sendMessageWithoutHistoryChange(
                    theoremStatement,
                    this.shots
                ).then((response) => {
                    llmResponse = response;
                }).catch((e) => {
                    this.runLogger.onException(e.message);
                    this.progressBar.finish();
                    llmResponse = e;
                });

                if (llmResponse instanceof Error) {
                    return GenerationResult.exception(llmResponse.message, "Open-ai completion request");
                }

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
            const cleanedProof = this.llmPrompt.cleanFromBrackets(foundProof);
            return GenerationResult.success(cleanedProof);
        } 

        return GenerationResult.searchFailed();
    }
}