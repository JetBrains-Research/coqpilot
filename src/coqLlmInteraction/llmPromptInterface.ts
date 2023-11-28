import { Theorem } from "../lib/pvTypes";
import { shuffleArray } from "./utils";
import logger from '../extension/logger';

class SeparatedTheorems {
    constructor(
        public readonly admittedTheorems: Theorem[],
        public readonly trainingTheorems: Theorem[], 
    ) {}
}

export type LLMPrompt = LlmPromptInterface & LlmPromptBase;

export interface LlmPromptInterface {
    /**
     * Gets the system message for the LLM. 
     * @returns The system message for the LLM.
     */
    getSystemMessage(): string;

    /**
     * Gets the message history for the LLM. 
     * @returns The message history for the LLM.
     */
    getMessageHistory(): { role: string; content: string; }[];
}    

export class LlmPromptBase {
    public readonly promptStrategy: string;
    theoremsFromFile: Theorem[] = [];
    trainingTheorems: Theorem[] = [];
    admittedTheorems: Theorem[] = [];

    constructor( 
        parsedFile: Theorem[],
        tokenLimit: number,
    ) {
        this.theoremsFromFile = parsedFile;
        this.promptStrategy = this.constructor.name;
        const separatedTheorems = this.computeTrainingTheorems(this.theoremsFromFile, tokenLimit);
        this.trainingTheorems = separatedTheorems.trainingTheorems;
        this.admittedTheorems = separatedTheorems.admittedTheorems;
    }

    countTokens = (str: string): number => {
        // Its hard enough to determine how gpt will
        // tokenize the string. Refer to the following
        // link for more information:
        // https://help.openai.com/en/articles/4936856-what-are-tokens-and-how-to-count-them
        // One token is approximately 4 characters.
        return (str.length / 4) >> 0;
    };

    static removeBackticks = (str: string): string => {
        return str.replace(/`/g, '');
    };

    static thrProofToBullet = (proof: string): string => {
        // Remove "Proof." and "Qed."
        let res = proof.replace(/Proof using\./g, '')
                       .replace(/Proof\./g, '')
                       .replace(/Qed\./g, '');

        return ` { ${res} }`;
    };

    cleanFromBrackets = (str: string): string => {
        return str.slice(2, str.length - 1).trim();
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
    computeTrainingTheorems(theorems: Theorem[], tokenLimit: number): SeparatedTheorems {
        let admittedTheoremsMaxTokenCount = 0;
        let theoremsTokensSum = 0;
        let provenTheorems: Theorem[] = [];
        let admittedTheorems: Theorem[] = [];

        for (const theorem of theorems) {
            if (!theorem.proof) {
                continue;
            } 

            if (theorem.proof.is_incomplete) {
                admittedTheoremsMaxTokenCount = Math.max(
                    admittedTheoremsMaxTokenCount,
                    this.countTokens(theorem.statement)
                );
                admittedTheorems.push(theorem);
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
        while (theoremsTokensSum > 0.95 * tokenLimit && provenTheorems.length > 0) {
            const theorem = provenTheorems.pop();
            if (!theorem || !theorem.proof) {
                continue;
            }

            theoremsTokensSum -= this.countTokens(theorem.statement) + this.countTokens(theorem.proof.onlyText());
        }

        const separated = new SeparatedTheorems(admittedTheorems, provenTheorems);
        logger.info(`Admitted theorems: ${separated.admittedTheorems.map((th) => th.name)}`);
        logger.info(`Training theorems: ${separated.trainingTheorems.map((th) => th.name)}`);
        return separated;
    }

    getAdmittedTheorems(): string[] {
        return this.admittedTheorems.map((th) => th.name);
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
}