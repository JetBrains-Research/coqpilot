/* eslint-disable @typescript-eslint/naming-convention */
import { Range } from "vscode-languageclient";

import { ProofGoal } from "../coqLsp/coqLspTypes";

export enum Vernacexpr {
    VernacLoad = "VernacLoad",
    VernacSyntaxExtension = "VernacSyntaxExtension",
    VernacOpenCloseScope = "VernacOpenCloseScope",
    VernacDelimiters = "VernacDelimiters",
    VernacBindScope = "VernacBindScope",
    VernacInfix = "VernacInfix",
    VernacNotation = "VernacNotation",
    VernacNotationAddFormat = "VernacNotationAddFormat",
    VernacDefinition = "VernacDefinition",
    VernacStartTheoremProof = "VernacStartTheoremProof",
    VernacEndProof = "VernacEndProof",
    VernacExactProof = "VernacExactProof",
    VernacAssumption = "VernacAssumption",
    VernacInductive = "VernacInductive",
    VernacFixpoint = "VernacFixpoint",
    VernacCoFixpoint = "VernacCoFixpoint",
    VernacScheme = "VernacScheme",
    VernacCombinedScheme = "VernacCombinedScheme",
    VernacUniverse = "VernacUniverse",
    VernacConstraint = "VernacConstraint",
    VernacBeginSection = "VernacBeginSection",
    VernacEndSegment = "VernacEndSegment",
    VernacRequire = "VernacRequire",
    VernacImport = "VernacImport",
    VernacCanonical = "VernacCanonical",
    VernacCoercion = "VernacCoercion",
    VernacIdentityCoercion = "VernacIdentityCoercion",
    VernacNameSectionHypSet = "VernacNameSectionHypSet",
    VernacInstance = "VernacInstance",
    VernacContext = "VernacContext",
    VernacDeclareInstances = "VernacDeclareInstances",
    VernacDeclareClass = "VernacDeclareClass",
    VernacDeclareModule = "VernacDeclareModule",
    VernacDefineModule = "VernacDefineModule",
    VernacDeclareModuleType = "VernacDeclareModuleType",
    VernacInclude = "VernacInclude",
    VernacSolveExistential = "VernacSolveExistential",
    VernacAddLoadPath = "VernacAddLoadPath",
    VernacRemoveLoadPath = "VernacRemoveLoadPath",
    VernacAddMLPath = "VernacAddMLPath",
    VernacDeclareMLModule = "VernacDeclareMLModule",
    VernacChdir = "VernacChdir",
    VernacWriteState = "VernacWriteState",
    VernacRestoreState = "VernacRestoreState",
    VernacResetName = "VernacResetName",
    VernacResetInitial = "VernacResetInitial",
    VernacBack = "VernacBack",
    VernacBackTo = "VernacBackTo",
    VernacCreateHintDb = "VernacCreateHintDb",
    VernacRemoveHints = "VernacRemoveHints",
    VernacHints = "VernacHints",
    VernacSyntacticDefinition = "VernacSyntacticDefinition",
    VernacDeclareImplicits = "VernacDeclareImplicits",
    VernacArguments = "VernacArguments",
    VernacArgumentsScope = "VernacArgumentsScope",
    VernacReserve = "VernacReserve",
    VernacGeneralizable = "VernacGeneralizable",
    VernacSetOpacity = "VernacSetOpacity",
    VernacSetStrategy = "VernacSetStrategy",
    VernacUnsetOption = "VernacUnsetOption",
    VernacSetOption = "VernacSetOption",
    VernacAddOption = "VernacAddOption",
    VernacRemoveOption = "VernacRemoveOption",
    VernacMemOption = "VernacMemOption",
    VernacPrintOption = "VernacPrintOption",
    VernacCheckMayEval = "VernacCheckMayEval",
    VernacGlobalCheck = "VernacGlobalCheck",
    VernacDeclareReduction = "VernacDeclareReduction",
    VernacPrint = "VernacPrint",
    VernacSearch = "VernacSearch",
    VernacLocate = "VernacLocate",
    VernacRegister = "VernacRegister",
    VernacComments = "VernacComments",
    VernacAbort = "VernacAbort",
    VernacAbortAll = "VernacAbortAll",
    VernacRestart = "VernacRestart",
    VernacUndo = "VernacUndo",
    VernacUndoTo = "VernacUndoTo",
    VernacBacktrack = "VernacBacktrack",
    VernacFocus = "VernacFocus",
    VernacUnfocus = "VernacUnfocus",
    VernacUnfocused = "VernacUnfocused",
    VernacBullet = "VernacBullet",
    VernacSubproof = "VernacSubproof",
    VernacEndSubproof = "VernacEndSubproof",
    VernacShow = "VernacShow",
    VernacCheckGuard = "VernacCheckGuard",
    VernacProof = "VernacProof",
    VernacProofMode = "VernacProofMode",
    VernacToplevelControl = "VernacToplevelControl",
    VernacExtend = "VernacExtend",
}

export class ProofStep {
    constructor(
        readonly text: string,
        readonly vernac_type: Vernacexpr,
        readonly range: Range
    ) {}

    toString(): string {
        return this.text;
    }
}

export class TheoremProof {
    constructor(
        readonly proof_steps: ProofStep[],
        readonly end_pos: Range,
        readonly is_incomplete: boolean,
        readonly holes: ProofStep[]
    ) {}

    toString(): string {
        let text = "";
        for (const step of this.proof_steps) {
            text +=
                step.toString() +
                (step.vernac_type !== Vernacexpr.VernacBullet ? "\n" : " ");
        }
        return text;
    }

    onlyText(): string {
        let text = "";
        for (const step of this.proof_steps) {
            text +=
                step.text.trim() +
                (step.vernac_type !== Vernacexpr.VernacBullet ? "\n" : " ");
        }
        return text;
    }
}

export class Theorem {
    constructor(
        readonly name: string,
        readonly statement_range: Range,
        readonly statement: string,
        readonly proof: TheoremProof,
        readonly initial_goal: ProofGoal | null = null
    ) {}

    toString(): string {
        let text = this.statement;
        text += "\n" + this.proof.toString();
        return text;
    }

    onlyText(): string {
        let text = this.statement;
        text += "\n" + this.proof.onlyText();
        return text;
    }
}
