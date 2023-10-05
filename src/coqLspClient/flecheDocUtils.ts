import { 
    Theorem,
    Vernacexpr, 
    ProofViewError, 
    TheoremProof, 
    ProofStep 
} from "../lib/pvTypes";

import {
    Position,
    Range, 
} from "vscode-languageclient";

import { 
    FlecheDocument,
    RangedSpan
} from "../lib/types";

function getExpr(span: RangedSpan): any[] {
    try {
        return span.span === null ? null : span.span['v']['expr'];
    } catch (error) {
        return null;
    }
}

function getTheoremName(expr: any[]): string {
    try {
        return expr[2][0][0][0]['v'][1];
    } catch (error) {
        throw new ProofViewError("Invalid theorem name");
    }
}

function getVernacexpr(expr: any[]): Vernacexpr {
    try {
        return expr[0] as Vernacexpr;
    } catch (error) {
        return null;
    }
}

function getProofEndCommand(expr: { [key: string]: any }): string {
    try {
        return expr[1][0];
    } catch (error) {
        return null;
    }
}

function checkIfExprEAdmit(expr: any[]): boolean {
    try {
        return getProofEndCommand(expr) === 'Admitted';
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
                text += '\n';
            }
            text += lines[i];
        }
        if (preserveLineBreaks) {
            text += '\n';
        }
        text += lines[end.line].substring(0, end.character);

        return text;
    }
}

function parseProof(
    spanIndex: number, 
    ast: RangedSpan[], 
    lines: string[],
): TheoremProof {
    let index = spanIndex;
    let proven = false;
    const proof: ProofStep[] = [];
    let endPos: Range | null = null;
    let proofContainsAdmit = false;

    while (!proven && index < ast.length) {
        const span = ast[index];

        const vernacType = getVernacexpr(getExpr(span));
        if (vernacType === Vernacexpr.VernacEndProof || vernacType === Vernacexpr.VernacAbort) {
            const proofStep = new ProofStep(
                getTextInRange(span.range.start, span.range.end, lines),
                vernacType,
                span.range
            );
            proof.push(proofStep);
            proven = true;
            endPos = span.range;
            // I assume when proof has some admitted parts it has either Admitted or Abort in the end
            // Isn't that right?
            if (checkIfExprEAdmit(getExpr(span)) || vernacType === Vernacexpr.VernacAbort) {
                proofContainsAdmit = true;
            }
        } else {
            const proofStep = new ProofStep(
                getTextInRange(span.range.start, span.range.end, lines),
                vernacType,
                span.range
            );

            proof.push(proofStep);
            index += 1;
        }
    }

    if (!proven || endPos === null) {
        throw new ProofViewError("Invalid or incomplete proof.");
    }

    const proofObj = new TheoremProof(proof, endPos, proofContainsAdmit);
    return proofObj;
}

export function parseFleche(
    doc: FlecheDocument, 
    textLines: string[],
): Theorem[] {
    if (doc === null) {
        throw new Error("Could not parse file");
    }

    const theorems: Theorem[] = [];
    for (let i = 0; i < doc.spans.length; i++) {
        const span = doc.spans[i];
        try {
            if (getVernacexpr(getExpr(span)) === Vernacexpr.VernacStartTheoremProof) {
                const thrName = getTheoremName(getExpr(span));
                const thrStatement = getTextInRange(
                    doc.spans[i].range.start, 
                    doc.spans[i].range.end, 
                    textLines,
                    true
                );
                
                const nextExprVernac = getVernacexpr(getExpr(doc.spans[i + 1]));
                if (i + 1 >= doc.spans.length) {
                    theorems.push(new Theorem(thrName, doc.spans[i].range, thrStatement, null));
                } else if (![
                    Vernacexpr.VernacProof, 
                    Vernacexpr.VernacAbort, 
                    Vernacexpr.VernacEndProof
                ].includes(nextExprVernac)) {
                    theorems.push(new Theorem(thrName, doc.spans[i].range, thrStatement, null));
                } else {
                    const proof = parseProof(i + 1, doc.spans, textLines);
                    theorems.push(new Theorem(thrName, doc.spans[i].range, thrStatement, proof));
                }
            } 
        } catch (error) {
            // Ignore
        }
    }

    return theorems;
}