import { SerializedGoal } from "../../../utils/coqUtils/goalParser";
import { TargetType } from "../../benchmarkingCore/completionGenerationTask";
import { SerializedCodeElementRange } from "../../common/codeElementPositions";

export interface LightweightCompletionGenerationTask {
    goalToProve: SerializedGoal;
    positionRange: SerializedCodeElementRange;
    targetType: TargetType;
    /**
     * Relative to the `workspacePath`.
     */
    relativeSourceFilePath: string;
    sourceTheoremName: string;
    /**
     * Relative to the project root.
     */
    relativeWorkspacePath: string;
}
