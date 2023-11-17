import { LLMPrompt } from './llmPromptInterface';
import { LLMIterator } from './llmIterator';
import { EvaluationLogger } from './evaluationLogger';
import { Uri } from 'vscode';
import logger from '../extension/logger';

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

    static editorError<T>(message: string | undefined = undefined): GenerationResult<T> {
        return new GenerationResult<T>(GenerationStatus.exception, message ?? "Editor error", "Editor");
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
    llmIterator: LLMIterator;
    logAttemps: boolean;
    logFilePath: string | null;
    contents: string[] | null;
    contentsPointer: number;
    timeout: number;
    runLogger: EvaluationLogger;
    shots: number;

    constructor(
        llmPrompt: LLMPrompt, 
        llmIterator: LLMIterator,
        logAttemps: boolean = false, 
        shots: number = 1,
        logFolderPath: string | null = null
    ) {
        this.llmPrompt = llmPrompt;
        this.llmIterator = llmIterator;
        this.logAttemps = logAttemps;

        this.llmIterator.initHistory(this.llmPrompt);
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
        fnVerifyProofs: (uri: Uri, proofs: LLMIterator, statement: string) => Promise<[string, boolean, string | null][]>
    ): Promise<GenerationResult<string>> {
        let proofCheckResult: [string, boolean, string | null][] | undefined = undefined;
        try {
            proofCheckResult = await fnVerifyProofs(uri, this.llmIterator, theoremStatement);
        } catch (e) {
            return GenerationResult.exception("Proof verification failed with " + e.message, "Interactor");
        }

        logger.info("Proof check result: " + JSON.stringify(proofCheckResult));
        this.runLogger.onTheoremProofStart();

        let foundProof: string | undefined = undefined;
        for (let i = 0; i < proofCheckResult.length; i++) {
            const [proof, proofStatus, errorMsg] = proofCheckResult[i];
            if (proofStatus) {
                this.runLogger.onSuccessAttempt(
                    i + 1, theoremName, 
                    theoremStatement, proof
                );
                foundProof = proof;
            } else {
                this.runLogger.onFailedAttempt(
                    i + 1, theoremName, 
                    theoremStatement, proof, errorMsg
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