import { lspmodels } from "coqlsp-client";
import { 
    existsSync, 
    mkdirSync, 
    writeFileSync,
    readFileSync,
    appendFileSync
} from "fs";
import { dirname, join } from "path";
import pino from 'pino';

export class EvalLoggingError extends Error {
    constructor(message: string) {
        super(message);
        this.name = "EvalLoggingError";
    }
}

export class EvaluationLogger {
    coqFile: string;
    logFilePath: string;
    contents: string[];
    insideProof: boolean = false;
    proofLog: string = "";
    proofComplete: boolean | null = null;
    contentsPointer: number = 0;
    statementsToRanges: { [key: string]: lspmodels.Range };
    rangesToText: { [range: string]: string } = {};
    logToFile: boolean;
    shots: number;
    logger = pino({
        name: 'ts-lsp-client',
        target: 'pino-pretty', // --target 'pino-pretty
        options: {
            levelFirst: true, // --levelFirst
            colorize: true,
            translateTime: true,
            ignore: 'pid,hostname' // --ignore
        }
    });

    constructor(
        coqFilePath: string, 
        runStrategy: string, 
        shots: number, 
        statements2ranges: { [key: string]: lspmodels.Range }, 
        logToFile: boolean = false,
        logFolderPath: string | null = null
    ) {
        this.coqFile = coqFilePath;

        if (logToFile) {
            const dateTimeNow = this.formatDate(new Date());
            const dirName = dirname(dirname(__dirname));
            const logFolder = logFolderPath ? logFolderPath : join(dirName, 'logs');     
            
            if (!existsSync(logFolder)) {
                mkdirSync(logFolder);
            }

            this.logFilePath = join(logFolder, `log_${dateTimeNow}.v`);

            const logFileContents = `(*\n Date: ${dateTimeNow}\n Strat: ${runStrategy}\n*)\n\n`;
            writeFileSync(this.logFilePath, logFileContents);
        }

        const coqFileContents = readFileSync(this.coqFile, "utf-8");
        this.contents = coqFileContents.split('\n');

        this.statementsToRanges = statements2ranges;
        this.logToFile = logToFile;   
        this.shots = shots;     
    }

    private formatDate = (date: Date): string => {
        const day = date.getDate();
        const month = date.getMonth() + 1;
        const hour = date.getHours();
        const minute = date.getMinutes();
        const second = date.getSeconds();

        return `${day}_${month}__${hour}_${minute}_${second}`;
    };

    private log2file(message: string) {
        appendFileSync(this.logFilePath, message);
    }

    private getTextInRange(
        start: lspmodels.Position, 
        end: lspmodels.Position, 
        preserveLineBreaks = true
    ): string {
        if (start.line === end.line) {
            return this.contents[start.line].substring(start.character, end.character);
        } else {
            let text = this.contents[start.line].substring(start.character);
            for (let i = start.line + 1; i < end.line; i++) {
                if (preserveLineBreaks) {
                    text += '\n';
                }
                text += this.contents[i];
            }
            if (preserveLineBreaks) {
                text += '\n';
            }
            text += this.contents[end.line].substring(0, end.character);

            return text;
        }
    }

    /**
     * Iterates over self.contents and substitutes
     * the ranges from self.ranges_to_text with
     * the corresponding text.
     */
    private substituteTextPieces() {
        let newText = "";
        const rangesTextPairs: [lspmodels.Range, string][] = [];
        for (const rangeString in this.rangesToText) {
            const range = JSON.parse(rangeString) as lspmodels.Range;
            rangesTextPairs.push([range, this.rangesToText[rangeString]]);
        }

        rangesTextPairs.sort((x, y) => {
            if (x[0].start.line !== y[0].start.line) {
                return x[0].start.line - y[0].start.line;
            } else {
                return x[0].start.character - y[0].start.character;
            }
        });

        let lastRangeEndPos: lspmodels.Position = {line: 0, character: 0};
        for (const [range, textPiece] of rangesTextPairs) {
            // Add the text between the last range and the start of the current range
            newText += this.getTextInRange(lastRangeEndPos, range.start);
            // Add the text of the current range
            newText += textPiece;
            lastRangeEndPos = range.end;
        }

        // Add the text after the last range
        newText += this.getTextInRange(
            lastRangeEndPos,
            {line: this.contents.length - 1, character: this.contents[this.contents.length - 1].length}
        );

        return newText;
    }

    onStartLlmResponseFetch(thrName: string) {
        this.logger.info(`Fetching potential proofs for theorem ${thrName}`);
    }

    onEndLlmResponseFetch() {
        this.logger.info("Fetching potential proofs finished");
    }

    onTheoremProofStart() {
        if (this.insideProof) {
            throw new EvalLoggingError("Already in proof");
        }
        this.insideProof = true;
        this.proofComplete = false;
        this.proofLog = "(* {THEOREM PROOF LOG START} *)\n";
    }

    onSuccessAttempt(
        attemptIndex: number,
        thrName: string,
        statement: string,
        proof: string
    ) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} *)\n`;
        this.proofLog += `${statement}\n${proof}\n`;
        
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} successful *)\n\n`;
        this.proofLog += "(* {THEOREM PROOF LOG END} *)";
        this.logger.info(`Attempt ${attemptIndex} for theorem ${thrName} successful`);
        this.proofComplete = true;

        if (!this.logToFile) {
            const neededRange = this.statementsToRanges[statement];
            this.rangesToText[JSON.stringify(neededRange)] = `${statement}\n${proof}`;
        }
    }
    
    onFailedAttempt(
        attemptIndex: number,
        thrName: string,
        statement: string,
        proof: string,
        errorMsg: string
    ) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} *)\n`;
        this.proofLog += `(*\n${statement}\n${proof}\n*)\n`;
        
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} unsuccessful *)\n`;
        this.proofLog += `(* ERROR message: ${errorMsg} *)\n\n`;
    }

    onAttemptException(
        attemptIndex: number,
        thrName: string,
        errorMsg: string
    ) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} failed with an exception*)\n`;
        this.proofLog += `(* EXCEPTION message: ${errorMsg} *)\n\n`;
        this.logger.info(`Attempt ${attemptIndex} for theorem ${thrName} failed with an exception`);
    }

    onProofCheckFail(errorMsg: string) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        this.proofLog += `(* ProofView responded with an error: ${errorMsg} *)\n`;
    }

    onTheoremProofEnd(statement: string, correctProof: string) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        if (!this.proofComplete) {
            this.proofLog += `(* Correct proof was not found. Here is the one from original file. *)\n`;
            this.proofLog += `${statement}\n${correctProof}\n`;
            this.proofLog += "(* {THEOREM PROOF LOG END} *)";
        }
        this.insideProof = false;

        if (this.logToFile) {
            const neededRange = this.statementsToRanges[statement];
            this.rangesToText[JSON.stringify(neededRange)] = this.proofLog;
        }
    }

    onEvaluationFinish() {
        if (this.logToFile) {
            const newText = this.substituteTextPieces();
            this.log2file(newText);
        }
    }
}