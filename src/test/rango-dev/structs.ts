import { SerializedCodeElementRange } from "../../utils/codeElementPositions";

export interface RangoInput {
    theoremName: string;

    theoremRange: SerializedCodeElementRange;
    proofRange: SerializedCodeElementRange;

    relativeSourceFilePath: string;
    projectPath: string;
}
