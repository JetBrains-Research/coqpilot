import { ProofView, coqlspmodels, lspmodels, ProgressBar, CliProgressBar } from "coqlsp-client";
import * as assert from "assert";
import { 
    readFileSync,
    writeFileSync
} from "fs";
import { shuffleArray } from "./utils";

export class LlmPromptInterface {
    proofView: ProofView | undefined;
    public readonly coqFile: string;
    public readonly rootDir: string;
    public readonly promptStrategy: string;
    progressBar: ProgressBar;
    theoremsFromFile: coqlspmodels.Theorem[] = [];
    trainingTheorems: coqlspmodels.Theorem[] = [];
    public statementsToRanges: { [key: string]: lspmodels.Range } = {};
    cachedMessageHistory: { role: string; content: string; }[] | null = null;

    protected constructor(
        pathToCoqFile: string, 
        pathToRootDir: string,
        proofView: ProofView,
        progressBar: ProgressBar,
    ) {
        this.coqFile = pathToCoqFile;
        this.rootDir = pathToRootDir;
        this.promptStrategy = this.constructor.name;
        this.progressBar = progressBar;
        this.proofView = proofView;
    }

    saveSnapshotToDisk(
        parsedTheoremsPath: string,
    ) {
        writeFileSync(parsedTheoremsPath, JSON.stringify(this.theoremsFromFile));
    }

    static countTokens = (str: string): number => {
        return str.split(/(\s+)/).filter( e => e.trim().length > 0).length;
    };

    /**
     * When we send a request to gpt, it has an upper limit on the number of tokens.
     * Number of tokens in our case, as we make a request for a single theorem not continuing the 
     * chat, will be system_message.size + all_theorems_statements_with_proofs.size + new_statement.size
     * 
     * When working with huge files, we cannot send all the solved theorems from the 
     * file as "train" theorems, because we will reach the token limit. This is why we need to 
     * heuristically choose the train theorems. For now we will choose theorems randomly. 
     * 
     * @param theorems List of all theorems in the file.
     * @param tokenLimit The token limit for the request.
     * @returns List of theorems to use for training.
     */
    static getTrainingTheorems(theorems: coqlspmodels.Theorem[], tokenLimit: number): coqlspmodels.Theorem[] {
        let admittedTheoremsMaxTokenCount = 0;
        let theoremsTokensSum = 0;
        let provenTheorems: coqlspmodels.Theorem[] = [];

        for (const theorem of theorems) {
            if (!theorem.proof) {
                continue;
            } 
             
            if (theorem.proof.is_incomplete) {
                admittedTheoremsMaxTokenCount = Math.max(
                    admittedTheoremsMaxTokenCount,
                    this.countTokens(theorem.statement)
                );
            } else {
                theoremsTokensSum += this.countTokens(theorem.statement) + this.countTokens(theorem.proof.onlyText());
                provenTheorems.push(theorem);
            }
        }
        theoremsTokensSum += admittedTheoremsMaxTokenCount;

        // We collected all the solved theorems from the file to an auxiliary list, we 
        // shuffle it and then pop theorems from it until the sum of their tokens + maximum
        // possible statement.size is greater than the token limit.
        shuffleArray(provenTheorems);
        while (theoremsTokensSum > 0.9 * tokenLimit && provenTheorems.length > 0) {
            const theorem = provenTheorems.pop();
            if (!theorem.proof) {
                continue;
            }

            theoremsTokensSum -= this.countTokens(theorem.statement) + this.countTokens(theorem.proof.onlyText());
        }

        return provenTheorems;
    }

    static async initFromSnapshot(
        messageHistoryPath: string,
        pathToCoqFile: string,
        pathToRootDir: string,
        tokenLimit: number,
        proofView: ProofView | undefined = undefined,
        progressBar: ProgressBar | undefined = new CliProgressBar(),
    ): Promise<LlmPromptInterface> {
        const theoremsFromFile = JSON.parse(readFileSync(messageHistoryPath, "utf-8")) as coqlspmodels.Theorem[];

        return await LlmPromptInterface.init(
            pathToCoqFile,
            pathToRootDir,
            tokenLimit,
            proofView,
            progressBar,
            theoremsFromFile
        );
    }

    static async init(
        pathToCoqFile: string, 
        pathToRootDir: string,
        tokenLimit: number,
        proofView: ProofView | undefined = undefined,
        progressBar: ProgressBar | undefined = new CliProgressBar(),
        theoremsFromFile: coqlspmodels.Theorem[] | undefined = undefined,
    ): Promise<LlmPromptInterface> {
        const proofViewToUse = proofView ? proofView : await ProofView.init(pathToCoqFile, pathToRootDir, progressBar);

        const llmPrompt = new LlmPromptInterface(
            pathToCoqFile,
            pathToRootDir,
            proofViewToUse,
            progressBar
        );

        llmPrompt.theoremsFromFile = theoremsFromFile ? theoremsFromFile : await llmPrompt.proofView.parseFile();
        llmPrompt.trainingTheorems = LlmPromptInterface.getTrainingTheorems(llmPrompt.theoremsFromFile, tokenLimit);

        try {
            llmPrompt.statementsToRanges = llmPrompt.theoremsFromFile
                .reduce((acc: { [key: string]: lspmodels.Range }, th: coqlspmodels.Theorem) => {
                    acc[th.statement] = {
                        start: th.statement_range.start,
                        end: th.proof.end_pos.end
                    };

                    return acc;
                }, {});
        } catch (e) {
            throw new Error("Some theorems in the file do not have proofs.");
        }

        return llmPrompt;
    }

    /**
     * Gets the system message for the LLM. 
     * @returns The system message for the LLM.
     */
    getSystemMessage(): string {
        throw new Error("Inherit from LlmPromptInterface and implement getSystemMessage() method");
    }

    /**
     * Gets the message history for the LLM. 
     * @returns The message history for the LLM.
     */
    getMessageHistory(): { role: string; content: string; }[] {
        throw new Error("Inherit from LlmPromptInterface and implement getMessageHistory() method");
    }

    /**
     * Gets the statement of a theorem by its name.
     * @param thrName The name of the theorem.
     * @returns The statement of the theorem.
     */
    getTheoremStatementByName(thrName: string): string {
        const thr = this.theoremsFromFile.find((th) => th.name === thrName);
        if (!thr) {
            throw new Error(`Theorem ${thrName} not found`);
        }

        return thr.statement;
    }

    /**
     * Verifies k proofs using the ProofView class. Return 
     * a list of tuples (bool, str) where the first element
     * is the result of the verification and the second is
     * the error message if the verification failed.
     * Either verification stops when the first proof is
     * verified or all proofs are verified and failed.
     * 
     * @param thrStatement The statement of the theorem.
     * @param proofs An array of potential proofs.
     * @returns A list of tuples (bool, str) where the first element
     * is the result of the verification and the second is
     * the error message if the verification failed.
     */
    async verifyProofs(thrStatement: string, proofs: string[]): Promise<[boolean, string | null][]> {
        assert(this.proofView);
        let context = "";
        if (this.statementsToRanges) {
            context = readFileSync(this.coqFile, "utf-8");
            const thrLineIndex = this.statementsToRanges[thrStatement].start.line;
            context = context.split('\n').slice(0, thrLineIndex).join('\n');
        }

        return this.proofView.checkProofs(context, thrStatement, proofs);
    }

    /**
     * Restarts the ProofView class.
     */
    async restartProofView() {
        this.proofView = await ProofView.init(this.coqFile, this.rootDir, this.progressBar);
    }

    /**
     * Free up resources.
     */
    stop() {
        this.proofView?.exit();
    }
}