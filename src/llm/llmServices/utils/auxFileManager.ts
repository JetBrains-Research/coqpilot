import { ParsedPath } from "path";

import { ProofGoal } from "../../../coqLsp/coqLspTypes";

import { goalToTargetLemma } from "../../../core/exposedCompletionGeneratorUtils";

import { getErrorMessage } from "../../../utils/errors/errorsUtils";
import { throwError } from "../../../utils/errors/throwErrors";
import { deleteFile, readFile, writeToFile } from "../../../utils/fs/fileUtils";
import { exists } from "../../../utils/fs/pathUtils";
import { joinPaths, parsePath } from "../../../utils/fs/pathUtils";
import {
    CodeElementRange,
    fromRange,
} from "../../../utils/structures/codeElementPositions";

export const AUX_FILE_SUBSTRING = "coqpilot_aux";

export interface AuxLemma {
    name: string;
    statementRange: CodeElementRange;
    admittedProofRange: CodeElementRange;
    auxFilePath: string;
}

export enum AuxFileCreationMode {
    INSERT_HELPER_LEMMA,
    /**
     * Unfortunately, inserting helper lemma built of target goal
     * might fail if global variables are present in the file.
     * TODO: support making additional request to `coq-lsp` to
     * retrieve global context and remove it from the goal.
     *
     * So far, in order to mitigate global variables case for benchmarking,
     * `REUSE_SOURCE_THEOREM` can be used to leave the source theorem untouched:
     * this way, such tools as Rango will get the original theorem as input and
     * will generate its whole proof.
     */
    REUSE_SOURCE_THEOREM,
}

export interface AuxFileCreationArgs {
    sourceFilePath: string;
    targetGoal: ProofGoal;
    requestUniqueIdentifier: string;

    mode: AuxFileCreationMode;

    sourceTheoremName: string;
    sourceTheoremStatementRange: CodeElementRange;
    sourceTheoremProofRange: CodeElementRange;
}

/**
 * Since `CoqLspClient` rework, no aux files needed anymore to check proofs.
 * Therefore, this wrapper's only task is to built a theorem from the target goal
 * and to provide it to an external tool as input.
 */
export async function withAuxFile<T>(
    args: AuxFileCreationArgs,
    block: (auxLemma: AuxLemma) => Promise<T>
): Promise<T> {
    const auxLemma = createAuxFile(args);
    try {
        return await block(auxLemma);
    } finally {
        deleteFile(auxLemma.auxFilePath);
    }
}

function createAuxFile(args: AuxFileCreationArgs): AuxLemma {
    if (args.mode === AuxFileCreationMode.INSERT_HELPER_LEMMA) {
        return createAuxFileWithHelperLemma(args);
    } else {
        return createAuxFileWithSourceTheorem(args);
    }
}

function createAuxFileWithSourceTheorem(args: AuxFileCreationArgs): AuxLemma {
    // TODO: optimize copying the file without reading it completely, use async streams
    const lineToCopyFileToExclusive = args.sourceTheoremProofRange.end.line + 1;
    const sourceFileContent = readFile(args.sourceFilePath, (err) =>
        throwError(`Failed to create aux file: ${getErrorMessage(err)}`)
    );
    const auxFileLines = sourceFileContent
        .split("\n")
        .slice(0, lineToCopyFileToExclusive);

    const parsedSourcePath = parsePath(args.sourceFilePath);
    const auxFilePath = resolveAuxFilePath(
        parsedSourcePath,
        args.requestUniqueIdentifier
    );
    writeToFile(auxFileLines.join("\n"), auxFilePath, (err) => {
        throwError(`Failed to create aux file: ${getErrorMessage(err)}`);
    });

    return {
        name: args.sourceTheoremName,
        statementRange: args.sourceTheoremStatementRange,
        admittedProofRange: args.sourceTheoremProofRange,
        auxFilePath: auxFilePath,
    };
}

function createAuxFileWithHelperLemma(args: AuxFileCreationArgs): AuxLemma {
    const lineToCopyFileToExclusive =
        args.sourceTheoremStatementRange.start.line;
    // TODO: optimize copying the file without reading it completely, use async streams
    const sourceFileContent = readFile(args.sourceFilePath, (err) =>
        throwError(`Failed to create aux file: ${getErrorMessage(err)}`)
    );
    const auxFileLines = sourceFileContent
        .split("\n")
        .slice(0, lineToCopyFileToExclusive);

    const auxLemmaContent = buildAuxLemma(args.targetGoal);
    auxFileLines.push(...auxLemmaContent.lines());

    const parsedSourcePath = parsePath(args.sourceFilePath);
    const auxFilePath = resolveAuxFilePath(
        parsedSourcePath,
        args.requestUniqueIdentifier
    );
    writeToFile(auxFileLines.join("\n"), auxFilePath, (err) => {
        throwError(`Failed to create aux file: ${getErrorMessage(err)}`);
    });

    const lemmaStatementStartLine = lineToCopyFileToExclusive;
    const lemmaStatementEndLine =
        lemmaStatementStartLine + auxLemmaContent.statement.length - 1;
    const lemmaBodyStartLine = lemmaStatementEndLine + 1;

    return {
        name: auxLemmaContent.lemmaName,
        statementRange: fromRange({
            start: {
                line: lemmaStatementStartLine,
                character: 0,
            },
            end: {
                line: lemmaStatementEndLine,
                character: getLastLineLength(auxLemmaContent.statement),
            },
        }),
        admittedProofRange: fromRange({
            start: {
                line: lemmaBodyStartLine,
                character: 0,
            },
            end: {
                line: lemmaBodyStartLine + auxLemmaContent.body.length - 1,
                character: getLastLineLength(auxLemmaContent.body),
            },
        }),
        auxFilePath: auxFilePath,
    };
}

class AuxLemmaContent {
    constructor(
        readonly lemmaName: string,
        readonly statement: string[],
        readonly body: string[]
    ) {}

    lines(): string[] {
        return [...this.statement, ...this.body];
    }
}

function buildAuxLemma(targetGoal: ProofGoal): AuxLemmaContent {
    return new AuxLemmaContent(
        "helper_theorem",
        goalToTargetLemma(targetGoal).split("\n"),
        ["Proof.", "\tadmit.", "Admitted."]
    );
}

function resolveAuxFilePath(
    parsedSourcePath: ParsedPath,
    requestUniqueIdentifier: string
): string {
    const sourceFileName = parsedSourcePath.name;
    const sourceFileExtension = parsedSourcePath.ext;
    const parentDirPath = parsedSourcePath.dir;
    for (let i = 0; ; i++) {
        const auxFileName = `${sourceFileName}_${AUX_FILE_SUBSTRING}_${requestUniqueIdentifier}_${i}${sourceFileExtension}`;
        const auxFilePath = joinPaths(parentDirPath, auxFileName);
        if (!exists(auxFilePath)) {
            return auxFilePath;
        }
    }
}

function getLastLineLength(lines: string[]): number {
    return lines[lines.length - 1].length;
}
