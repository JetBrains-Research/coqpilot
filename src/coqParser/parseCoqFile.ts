import { readFileSync } from "fs";
import { Position, Range } from "vscode-languageclient";

import { CoqLspClientInterface } from "../coqLsp/coqLspClient";
import {
    CoqParsingError,
    FlecheDocument,
    Goal,
    PpString,
    RangedSpan,
} from "../coqLsp/coqLspTypes";

import { Uri } from "../utils/uri";

import { ProofStep, Theorem, TheoremProof, Vernacexpr } from "./parsedTypes";
import { Result } from "ts-results";

/**
 * TODO: [LspCoreRefactor] Refactor retrieveInitialGoal param 
 * to be something more reasonable and readable. 
 */
export async function parseCoqFile(
    uri: Uri,
    client: CoqLspClientInterface,
    retrieveInitialGoal: boolean = true
): Promise<Theorem[]> {
    return client
        .getFlecheDocument(uri)
        .then((doc) => {
            const documentText = readFileSync(uri.fsPath)
                .toString()
                .split("\n");
            return parseFlecheDocument(doc, documentText, client, uri, retrieveInitialGoal);
        })
        .catch((error) => {
            throw new CoqParsingError(
                `failed to parse file with Error: ${error.message}`
            );
        });
}

async function parseFlecheDocument(
    doc: FlecheDocument,
    textLines: string[],
    client: CoqLspClientInterface,
    uri: Uri,
    retrieveInitialGoal: boolean
): Promise<Theorem[]> {
    if (doc === null) {
        throw Error("could not parse file");
    }

    const theorems: Theorem[] = [];
    for (let i = 0; i < doc.spans.length; i++) {
        const span = doc.spans[i];
        try {
            const vernacType = getVernacexpr(getExpr(span));
            if (
                vernacType &&
                [
                    Vernacexpr.VernacDefinition,
                    Vernacexpr.VernacStartTheoremProof,
                ].includes(vernacType)
            ) {
                const thrName = getName(getExpr(span));
                const thrStatement = getTextInRange(
                    doc.spans[i].range.start,
                    doc.spans[i].range.end,
                    textLines,
                    true
                );

                const nextExprVernac = getVernacexpr(getExpr(doc.spans[i + 1]));
                if (i + 1 >= doc.spans.length) {
                    theorems.push(
                        new Theorem(
                            thrName,
                            doc.spans[i].range,
                            thrStatement,
                            null,
                            null
                        )
                    );
                } else if (!nextExprVernac) {
                    throw new CoqParsingError("unable to parse proof");
                } else if (
                    ![
                        Vernacexpr.VernacProof,
                        Vernacexpr.VernacAbort,
                        Vernacexpr.VernacEndProof,
                    ].includes(nextExprVernac)
                ) {
                    theorems.push(
                        new Theorem(
                            thrName,
                            doc.spans[i].range,
                            thrStatement,
                            null,
                            null
                        )
                    );
                } else {
                     // TODO: [LspCoreRefactor] Discuss invariants on initial_goal
                     // and allow it's absence. As calculation of initial_goal
                     // brings overhead of 100ms per theorem.
                    let initialGoal: Result<Goal<PpString>[], Error> | null = null;
                    if (retrieveInitialGoal) {
                        initialGoal = await client.getGoalsAtPoint(
                            doc.spans[i + 1].range.start,
                            uri,
                            1
                        );

                        if (initialGoal.err) {
                            throw new CoqParsingError(
                                `unable to get initial goal for theorem: ${thrName}`
                            );
                        }
                    }

                    const proof = parseProof(i + 1, doc.spans, textLines);
                    theorems.push(
                        new Theorem(
                            thrName,
                            doc.spans[i].range,
                            thrStatement,
                            proof,
                            initialGoal?.val[0]
                        )
                    );
                }
            }
        } catch (error) {
            // Ignore
        }
    }

    return theorems;
}

function getExpr(span: RangedSpan): any[] | null {
    try {
        return span.span === null ? null : span.span["v"]["expr"][1];
    } catch (error) {
        return null;
    }
}

function getTheoremName(expr: any): string {
    try {
        return expr[2][0][0][0]["v"][1];
    } catch (error) {
        throw new CoqParsingError("invalid theorem name");
    }
}

function getDefinitionName(expr: any): string {
    try {
        return expr[2][0]["v"][1][1];
    } catch (error) {
        throw new CoqParsingError("invalid definition name");
    }
}

function getName(expr: any): string {
    switch (getVernacexpr(expr)) {
        case Vernacexpr.VernacDefinition:
            return getDefinitionName(expr);
        case Vernacexpr.VernacStartTheoremProof:
            return getTheoremName(expr);
        default:
            throw new CoqParsingError(`invalid name for expression: "${expr}"`);
    }
}

function getVernacexpr(expr: any): Vernacexpr | null {
    try {
        return expr[0] as Vernacexpr;
    } catch (error) {
        return null;
    }
}

function getProofEndCommand(expr: { [key: string]: any }): string | null {
    try {
        return expr[1][0];
    } catch (error) {
        return null;
    }
}

function checkIfExprEAdmit(expr: any): boolean {
    try {
        return getProofEndCommand(expr) === "Admitted";
    } catch (error) {
        return false;
    }
}

function getTextInRange(
    start: Position,
    end: Position,
    lines: string[],
    preserveLineBreaks = false
): string {
    if (start.line === end.line) {
        return lines[start.line].substring(start.character, end.character);
    } else {
        let text = lines[start.line].substring(start.character);
        for (let i = start.line + 1; i < end.line; i++) {
            if (preserveLineBreaks) {
                text += "\n";
            }
            text += lines[i];
        }
        if (preserveLineBreaks) {
            text += "\n";
        }
        text += lines[end.line].substring(0, end.character);

        return text;
    }
}

function parseProof(
    spanIndex: number,
    ast: RangedSpan[],
    lines: string[]
): TheoremProof {
    let index = spanIndex;
    let proven = false;
    const proof: ProofStep[] = [];
    let endPos: Range | null = null;
    let proofContainsAdmit = false;
    let proofHoles: ProofStep[] = [];

    while (!proven && index < ast.length) {
        const span = ast[index];

        const vernacType = getVernacexpr(getExpr(span));
        if (!vernacType) {
            throw new CoqParsingError(
                "unable to derive the vernac type of the sentence"
            );
        }

        if (
            vernacType === Vernacexpr.VernacEndProof ||
            vernacType === Vernacexpr.VernacAbort
        ) {
            const proofStep = new ProofStep(
                getTextInRange(span.range.start, span.range.end, lines),
                vernacType,
                span.range
            );
            proof.push(proofStep);
            proven = true;
            endPos = span.range;

            if (
                checkIfExprEAdmit(getExpr(span)) ||
                vernacType === Vernacexpr.VernacAbort
            ) {
                proofContainsAdmit = true;
            }
        } else {
            const proofText = getTextInRange(
                span.range.start,
                span.range.end,
                lines
            );
            const proofStep = new ProofStep(proofText, vernacType, span.range);

            proof.push(proofStep);
            index += 1;

            if (proofText.includes("admit")) {
                proofHoles.push(proofStep);
            }
        }
    }

    if (!proven || endPos === null) {
        throw new CoqParsingError("invalid or incomplete proof");
    }

    const proofObj = new TheoremProof(
        proof,
        endPos,
        proofContainsAdmit,
        proofHoles
    );
    return proofObj;
}
