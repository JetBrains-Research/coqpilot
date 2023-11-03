import { 
    existsSync, 
    mkdirSync, 
    writeFileSync,
    appendFileSync
} from "fs";
import { dirname, join } from "path";
import logger from "../extension/logger";

export class EvalLoggingError extends Error {
    constructor(message: string) {
        super(message);
        this.name = "EvalLoggingError";
    }
}

export class EvaluationLogger {
    debugLogPath: string;
    insideProof: boolean = false;
    proofLog: string = "";
    proofComplete: boolean | null = null;
    contentsPointer: number = 0;
    shots: number;
    logToFile: boolean;
    holeProofAttemtsLog: string = "";

    constructor(
        runStrategy: string, 
        shots: number, 
        logToFile: boolean = false,
        logFolderPath: string | null = null
    ) {
        this.logToFile = logToFile;
        if (logToFile) {
            const dateTimeNow = EvaluationLogger.formatDate(new Date());
            const dirName = dirname(dirname(__dirname));
            const logFolder = logFolderPath ?? join(dirName, 'logs');     
            
            if (!existsSync(logFolder)) {
                mkdirSync(logFolder);
            }

            this.debugLogPath = join(logFolder, `debug_log_${dateTimeNow}.txt`);

            if (existsSync(this.debugLogPath)) {
                const randomNum = Math.floor(Math.random() * 1000);
                this.debugLogPath = join(logFolder, `debug_log_${dateTimeNow}_${randomNum}.txt`);
            }

            const logFileContents = `(*\n Date: ${dateTimeNow}\n Strat: ${runStrategy}\n*)\n\n`;
            writeFileSync(this.debugLogPath, logFileContents);
        }

        this.shots = shots;     
    }

    static formatDate = (date: Date): string => {
        const day = date.getDate();
        const month = date.getMonth() + 1;
        const hour = date.getHours();
        const minute = date.getMinutes();

        return `${day}_${month}__${hour}_${minute}`;
    };

    onStartLlmResponseFetch(thrName: string) {
        logger.info(`Fetching potential proofs for theorem ${thrName}`);
    }

    onStartLlmResponseFetchForHole(thrName: string, holeNum: number) {
        logger.info(`Fetching potential proofs for hole ${holeNum} of theorem ${thrName}`);
    }

    onEndLlmResponseFetch() {
        logger.info("Fetching potential proofs finished");
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
        this.proofLog += `${statement}\nProof.\n${proof}\nQed.\n`;
        
        this.proofLog += `(* Attempt ${attemptIndex} for theorem ${thrName} successful *)\n\n`;
        this.proofLog += "(* {THEOREM PROOF LOG END} *)";
        logger.info(`Attempt ${attemptIndex} for theorem ${thrName} successful`);
        this.proofComplete = true;
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
        this.proofLog += `(*\n${statement}\nProof.\n${proof}\nQed.\n*)\n`;
        
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
        logger.info(`Attempt ${attemptIndex} for theorem ${thrName} failed with an exception`);
    }

    onException(errorMsg: string) {
        logger.error(`Exception: ${errorMsg}`);
        if (this.insideProof) {
            this.proofLog += `(* Exception: ${errorMsg} *)\n`;
        }
    }

    onProofCheckFail(errorMsg: string) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        this.proofLog += `(* ProofView responded with an error: ${errorMsg} *)\n`;
    }

    onTheoremProofEnd(statement: string) {
        if (!this.insideProof) {
            throw new EvalLoggingError("Not in proof");
        }
        if (!this.proofComplete) {
            this.proofLog += `(* Correct proof was not found. This theorem will remain Admitted. *)\n`;
            this.proofLog += `${statement}\nAdmitted.\n`;
            this.proofLog += "(* {THEOREM PROOF LOG END} *)";
        }
        this.insideProof = false;
        this.holeProofAttemtsLog += this.proofLog;

        if (this.logToFile) {
            appendFileSync(this.debugLogPath, `\n${this.proofLog}\n`);
        }
    }

    resetResourses() {
        this.insideProof = false;
        this.proofLog = "";
        this.proofComplete = null;
        this.contentsPointer = 0;
    }

    onEvaluationFinish() {
        this.resetResourses();
    }
}