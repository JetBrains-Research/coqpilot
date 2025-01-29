/* eslint-disable @typescript-eslint/naming-convention */
import {
    Position,
    Range,
    TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
} from "vscode-languageclient";

import { buildErrorCompleteLog } from "../utils/errorsUtils";

export type ProofGoal = Goal<PpString>;

export interface Hyp<Pp> {
    names: Pp[];
    def?: Pp;
    ty: Pp;
}

export interface Goal<Pp> {
    ty: Pp;
    hyps: Hyp<Pp>[];
}

export interface GoalConfig<Pp> {
    goals: Goal<Pp>[];
    stack: [Goal<Pp>[], Goal<Pp>[]][];
    bullet?: Pp;
    shelf: Goal<Pp>[];
    given_up: Goal<Pp>[];
}

export interface Message<Pp> {
    range?: Range;
    level: number;
    text: Pp;
}

export type Id = ["Id", string];

export interface Loc {
    fname: any;
    line_nb: number;
    bol_pos: number;
    line_nb_last: number;
    bol_pos_last: number;
    bp: number;
    ep: number;
}

export interface Obl {
    name: Id;
    loc?: Loc;
    status: [boolean, any];
    solved: boolean;
}

export interface OblsView {
    opaque: boolean;
    remaining: number;
    obligations: Obl[];
}

export type ProgramInfo = [Id, OblsView][];

export interface GoalAnswer<Pp> {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
    goals?: GoalConfig<Pp>;
    program?: ProgramInfo;
    messages: Pp[] | Message<Pp>[];
    error?: Pp;
}

export interface GoalRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
    pp_format?: "Pp" | "Str";
    command?: string;
    mode?: "Prev" | "After";
}

export type Pp =
    | ["Pp_empty"]
    | ["Pp_string", string]
    | ["Pp_glue", Pp[]]
    | ["Pp_box", any, Pp]
    | ["Pp_tag", any, Pp]
    | ["Pp_print_break", number, number]
    | ["Pp_force_newline"]
    | ["Pp_comment", string[]];

export type PpString = Pp | string;

/**
 * Quick and dirty utility function to convert a pretty-printing object into a plain string.
 */
export function convertToString(pp: PpString): string {
    if (typeof pp === "string") {
        return pp;
    }
    switch (pp[0]) {
        case "Pp_empty":
        case "Pp_comment":
            return "";
        case "Pp_string":
            return pp[1];
        case "Pp_glue":
            return pp[1].map(convertToString).join("");
        case "Pp_box":
        case "Pp_tag":
            return convertToString(pp[2]);
        case "Pp_print_break":
            return " ";
        case "Pp_force_newline":
            return "\n";
    }
}

export interface FlecheDocumentParams {
    textDocument: TextDocumentIdentifier;
}

// Status of the document, Yes if fully checked, range contains the last seen lexical token
interface CompletionStatus {
    status: ["Yes" | "Stopped" | "Failed"];
    range: Range;
}

// Implementation-specific span information, for now the serialized Ast if present.
type SpanInfo = any;

export interface RangedSpan {
    range: Range;
    span?: SpanInfo;
}

export interface FlecheDocument {
    spans: RangedSpan[];
    completed: CompletionStatus;
}

export interface FlecheSaveParams {
    textDocument: VersionedTextDocumentIdentifier;
}

export interface SentencePerfParams {
    loc: Loc;
    time: number;
    mem: number;
}

export interface DocumentPerfParams {
    summary: string;
    timings: SentencePerfParams[];
}

export class CoqLspError extends Error {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CoqLspError";
    }

    static unknownError(err?: any): CoqLspError {
        const errorLog =
            err === undefined ? "" : `:\n${buildErrorCompleteLog(err)}`;
        return new CoqLspError(
            `Unknown CoqLSP error, please report this issue${errorLog}`
        );
    }
}

export class CoqParsingError extends CoqLspError {
    constructor(
        message: string,
        public data?: any
    ) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CoqParsingError";
    }
}

export class CoqLspTimeoutError extends CoqLspError {
    constructor(message: string) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CoqLspTimeoutError";
    }
}

export class CoqLspStartupError extends CoqLspError {
    constructor(
        message: string,
        readonly path: string
    ) {
        super(message);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "CoqLspStartupError";
    }
}
