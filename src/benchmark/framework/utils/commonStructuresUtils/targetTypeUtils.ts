import { TargetType } from "../../../../core/completionGenerationContext";

import { TargetRequestType } from "../../structures/common/inputTargets";

export function toTargetType(requestType: TargetRequestType): TargetType {
    switch (requestType) {
        case TargetRequestType.ALL_ADMITS:
            return TargetType.ADMIT;
        case TargetRequestType.THEOREM_PROOF:
            return TargetType.PROVE_THEOREM;
    }
}
