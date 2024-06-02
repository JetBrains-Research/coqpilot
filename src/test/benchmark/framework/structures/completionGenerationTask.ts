import * as path from "path";

import { CoqLspClient } from "../../../../coqLsp/coqLspClient";
import { Goal, PpString } from "../../../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../../core/completionGenerator";

import { CodeElementRange, TheoremData } from "./utilStructures";

export class CompletionGenerationTask {
    constructor(
        readonly targetGoalToProve: Goal<PpString>,
        readonly targetPositionRange: CodeElementRange,
        readonly preparedEnvironment: PreparedBenchmarkingTaskEnvironment,
        readonly sourceTheorem: TheoremData,
        readonly workspaceRoot: WorkspaceRoot | undefined
    ) {}

    readonly sourceFilePath =
        this.preparedEnvironment.parsedSourceFileData.filePath;
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
            this.preparedEnvironment.parsedSourceFileData
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

export interface PreparedBenchmarkingTaskEnvironment {
    coqLspClient: CoqLspClient;
    parsedSourceFileData: ParsedCoqFileData;
}

export interface ParsedCoqFileData {
    /**
     * All theorems that were successfully parsed from the file.
     * Ones that don't end with `Qed.` are also included.
     */
    allFileTheorems: TheoremData[];

    fileLines: string[];
    fileVersion: number;
    filePath: string;
}

export interface WorkspaceRoot {
    /**
     * This path is expected to be an absolute resolved path inside the `dataset` directory.
     */
    directoryPath: string;
    requiresNixEnvironment: boolean;
}
