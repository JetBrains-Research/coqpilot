import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { TargetType } from "../../../../core/completionGenerationContext";
import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerationContext";

import {
    EqualTo,
    HashUtils,
} from "../../../../utils/collectionUtils/equalityUtils";
import { CodeElementRange } from "../../../../utils/structures/codeElementPositions";
import { goalToProveAsString } from "../../utils/coqUtils/goalParser";
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
    readonly targetGoalToProveAsString = goalToProveAsString(
        this.targetGoalToProve
    );

    getCompletionContext(): CompletionContext {
        return {
            proofGoal: this.targetGoalToProve,
            admitRange: this.targetPositionRange,
            sourceTheorem: this.sourceTheorem.sourceTheorem,
            targetType: this.targetType,
        };
    }

    getSourceFileEnvironment(): SourceFileEnvironment {
        return this.parsedSourceFileData.constructSourceFileEnvironment(
            this.workspaceRoot
        );
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
