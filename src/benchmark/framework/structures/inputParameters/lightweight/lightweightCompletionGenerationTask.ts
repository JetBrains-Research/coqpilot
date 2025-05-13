import { TargetType } from "../../../../../core/completionGenerationContext";

import { SerializedCodeElementRange } from "../../../../../utils/structures/codeElementPositions";
import { SerializedGoal } from "../../../utils/coqUtils/goalParser";

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
