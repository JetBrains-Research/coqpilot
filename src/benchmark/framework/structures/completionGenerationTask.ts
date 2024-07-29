import { ProofGoal } from "../../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    SourceFileEnvironment,
} from "../../../core/completionGenerationContext";

import { EqualTo, HashUtils } from "../utils/equalitySet";
import { getDatasetDir } from "../utils/fsUtils";

import { ParsedCoqFileData } from "./parsedCoqFileData";
import { TheoremData } from "./theoremData";
import { CodeElementRange } from "./utilStructures";

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

export interface WorkspaceRoot {
    /**
     * This path is expected to be an absolute resolved path inside the `dataset` directory.
     */
    directoryPath: string;
    requiresNixEnvironment: boolean;
}

/**
 * Mock `WorkspaceRoot` for target files that do not have an actual workspace.
 *
 * When working with `WorkspaceRoot` object, it should be checked via `isNoWorkspaceRoot` function.
 * In case it is indeed this mock `noWorkspaceRoot`, it should be handled as a special case.
 *
 * Implementation note: `noWorkspaceRoot` was chosen instead of `undefined` due to
 * its better support as a key of `Map` and general convenience of paths resolving.
 */
export const noWorkspaceRoot: WorkspaceRoot = {
    directoryPath: getDatasetDir(),
    requiresNixEnvironment: false,
};

export function isNoWorkspaceRoot(workspaceRoot: WorkspaceRoot): boolean {
    return workspaceRoot === noWorkspaceRoot;
}
