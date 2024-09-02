import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import { EqualTo, HashUtils } from "../../utils/equalitySet";
import { CodeElementRange } from "../common/codeElementPositions";
import { WorkspaceRoot } from "../common/workspaceRoot";
import { ParsedCoqFileData } from "../parsedCoqFile/parsedCoqFileData";
import { TheoremData } from "../parsedCoqFile/theoremData";

export class CompletionGenerationTask
    implements EqualTo<CompletionGenerationTask>
{
    constructor(
        readonly targetGoalToProve: ProofGoal,
        readonly targetPositionRange: CodeElementRange,
        readonly targetType: TargetType,
        readonly parsedSourceFileData: ParsedCoqFileData,
        readonly sourceTheorem: TheoremData,
        readonly workspaceRoot: WorkspaceRoot
    ) {}

    readonly sourceFilePath = this.parsedSourceFileData.filePath;
    readonly targetGoalToProveAsString = `${this.targetGoalToProve.ty}`;

    getCompletionContext(): CompletionContext {
        return {
            proofGoal: this.targetGoalToProve,
            prefixEndPosition: this.targetPositionRange.start,
            admitEndPosition: this.targetPositionRange.end,
        };
    }

    getSourceFileEnvironment(): SourceFileEnvironment {
        return this.parsedSourceFileData.constructSourceFileEnvironment();
    }

    equalTo(other: CompletionGenerationTask): boolean {
        return (
            this.sourceFilePath === other.sourceFilePath &&
            this.targetType === other.targetType &&
            this.targetPositionRange.equalsTo(other.targetPositionRange)
        );
    }

    hash(): number {
        return HashUtils.hashAsStrings(
            this.sourceFilePath,
            this.targetType,
            this.targetPositionRange.toString()
        );
    }
}

export enum TargetType {
    ADMIT = "ADMIT",
    PROVE_THEOREM = "PROVE_THEOREM",
}
