import { Mutex } from "async-mutex";
import { appendFileSync, existsSync, unlinkSync, writeFileSync } from "fs";
import * as path from "path";
import { Err, Ok, Result } from "ts-results";
import { Position } from "vscode-languageclient";

import { CoqLspClient, DiagnosticMessage } from "../../coqLsp/coqLspClient";
import { Goal, Message, PpString } from "../../coqLsp/coqLspTypes";

import { Uri } from "../../utils/uri";

export type CoqCodeExecError = string;
export type CoqCodeExecGoalResult = Result<Goal<PpString>, CoqCodeExecError>;
export type CoqCommandExecResult = Result<string[], CoqCodeExecError>;

/**
 * Logic is similar to CoqProofChecker, yet, I decided
 * not to add them up, as the server project is now
 * experimental and I want to keep the changes to the
 * initial codebase minimal.
 */
export interface CoqCodeExecutorInterface {
    /**
     * Works similar to CoqProofChecker.checkProofs but
     * with slightly different semantics. This function
     * executes the given Coq code in specified environment
     * and returns either the goal after the execution or
     * an error message occured in the provided code.
     * @param sourceDirPath Parent directory of the source file
     * @param sourceFileContentPrefix Prefix with which to typecheck the code
     * @param prefixEndPosition The position after the prefix end
     * @param coqCode Coq code to execute
     */
    getGoalAfterCoqCode(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCode: string
    ): Promise<CoqCodeExecGoalResult>;

    executeCoqCommand(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCommand: string
    ): Promise<CoqCommandExecResult>;
}

export class CoqCodeExecutor implements CoqCodeExecutorInterface {
    private mutex: Mutex = new Mutex();

    constructor(private coqLspClient: CoqLspClient) {}

    async getGoalAfterCoqCode(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCode: string,
        coqLspTimeoutMillis: number = 150000
    ): Promise<CoqCodeExecGoalResult> {
        return this.executeWithTimeout(
            this.getGoalAfterCoqCodeUnsafe(
                sourceDirPath,
                sourceFileContentPrefix,
                prefixEndPosition,
                coqCode
            ),
            coqLspTimeoutMillis
        );
    }

    async executeCoqCommand(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCode: string,
        coqLspTimeoutMillis: number = 150000
    ): Promise<CoqCommandExecResult> {
        return this.executeWithTimeout(
            this.executeCoqCommandUnsafe(
                sourceDirPath,
                sourceFileContentPrefix,
                prefixEndPosition,
                coqCode
            ),
            coqLspTimeoutMillis
        );
    }

    private async executeWithTimeout<T>(
        promise: Promise<T>,
        timeoutMillis: number
    ): Promise<T> {
        return await this.mutex.runExclusive(async () => {
            const timeoutPromise = new Promise<T>((_, reject) => {
                setTimeout(() => {
                    reject(
                        new Error(
                            `executeCoqCode timed out after ${timeoutMillis} milliseconds`
                        )
                    );
                }, timeoutMillis);
            });

            return Promise.race([promise, timeoutPromise]);
        });
    }

    // TODO: This is duplicate with CoqProofChecker.makeAuxFileName
    // Make sense to make it a global utility function
    private makeAuxFileName(
        sourceDirPath: string,
        unique: boolean = true
    ): Uri {
        const defaultAuxFileName = "agent_request_cp_aux.v";
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

    private async getGoalAfterCoqCodeUnsafe(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCode: string
    ): Promise<CoqCodeExecGoalResult> {
        const auxFileUri = this.makeAuxFileName(sourceDirPath);
        const diagnostic = await this.getDiagnosticAfterExec(
            auxFileUri,
            sourceFileContentPrefix,
            coqCode
        );

        if (diagnostic) {
            return Err(diagnostic);
        }

        const coqCodeLines = coqCode.split("\n");
        const codeEndPos = {
            line: prefixEndPosition.line + 2 + coqCodeLines.length,
            character: coqCode.at(-1)?.length || 0,
        };

        const goal = await this.coqLspClient.getFirstGoalAtPoint(
            codeEndPos,
            auxFileUri,
            2
        );

        unlinkSync(auxFileUri.fsPath);

        if (!(goal instanceof Error)) {
            return Ok(goal);
        } else {
            return Err(goal.message);
        }
    }

    private formatLspMessages(messages: PpString[] | Message<PpString>[]): string[] {
        return messages.map((message) => {
            if (typeof message === "string") {
                return message;
            }

            return (message as Message<PpString>).text.toString();
        });
    }

    private async executeCoqCommandUnsafe(
        sourceDirPath: string,
        sourceFileContentPrefix: string[],
        prefixEndPosition: Position,
        coqCommand: string
    ): Promise<CoqCommandExecResult> {
        if (coqCommand.includes("\n")) {
            return Err("Coq command must be a single line");
        }

        const auxFileUri = this.makeAuxFileName(sourceDirPath);
        const diagnostic = await this.getDiagnosticAfterExec(
            auxFileUri,
            sourceFileContentPrefix,
            coqCommand
        );

        if (diagnostic) {
            return Err(diagnostic);
        }

        const commandMessagePos = {
            line: prefixEndPosition.line + 2,
            character: coqCommand.length - 1,
        };

        const message = await this.coqLspClient.getMessageAtPoint(
            commandMessagePos,
            auxFileUri,
            2
        );

        unlinkSync(auxFileUri.fsPath);

        if (!(message instanceof Error)) {
            return Ok(this.formatLspMessages(message));   
        } else {
            return Err(message.message);
        }
    }

    private async getDiagnosticAfterExec(
        auxFileUri: Uri,
        sourceFileContentPrefix: string[],
        coqCode: string
    ): Promise<DiagnosticMessage> {
        const sourceFileContent = sourceFileContentPrefix.join("\n");
        writeFileSync(auxFileUri.fsPath, sourceFileContent);
        await this.coqLspClient.openTextDocument(auxFileUri);

        const appendedSuffix = `\n\n${coqCode}`;
        appendFileSync(auxFileUri.fsPath, appendedSuffix);

        return await this.coqLspClient.updateTextDocument(
            sourceFileContentPrefix,
            appendedSuffix,
            auxFileUri,
            2
        );
    }
}
