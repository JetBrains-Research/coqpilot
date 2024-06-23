import * as path from "path";

import { Goal, PpString } from "../../../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerator";

import { ParsedCoqFileData } from "./parsedCoqFileData";
import { TheoremData } from "./theoremData";
import { CodeElementRange } from "./utilStructures";

export class CompletionGenerationTask {
    constructor(
        readonly targetGoalToProve: Goal<PpString>,
        readonly targetPositionRange: CodeElementRange,
        readonly targetType: TargetType,
        readonly parsedSourceFileData: ParsedCoqFileData,
        readonly sourceTheorem: TheoremData,
        readonly workspaceRoot: WorkspaceRoot | undefined
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
        return CompletionGenerationTask.constructSourceFileEnvironment(
            this.parsedSourceFileData
        );
    }

    private static constructSourceFileEnvironment(
        parsedFileData: ParsedCoqFileData
    ): SourceFileEnvironment {
        return {
            fileTheorems: parsedFileData.allFileTheorems
                .filter(
                    (theoremData) =>
                        theoremData.proof && !theoremData.proof.is_incomplete
                )
                .map((theoremData) => theoremData.theorem),
            fileLines: parsedFileData.fileLines,
            fileVersion: parsedFileData.fileVersion,
            dirPath: path.dirname(parsedFileData.filePath),
        };
    }
}

export enum TargetType {
    ADMIT,
    PROVE_THEOREM,
}

export interface WorkspaceRoot {
    /**
     * This path is expected to be an absolute resolved path inside the `dataset` directory.
     */
    directoryPath: string;
    requiresNixEnvironment: boolean;
}
