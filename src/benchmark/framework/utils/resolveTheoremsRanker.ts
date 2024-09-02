import { JaccardIndexContextTheoremsRanker } from "../../../core/contextTheoremRanker/JaccardIndexContextTheoremsRanker";
import { ContextTheoremsRanker } from "../../../core/contextTheoremRanker/contextTheoremsRanker";
import { DistanceContextTheoremsRanker } from "../../../core/contextTheoremRanker/distanceContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../../../core/contextTheoremRanker/randomContextTheoremsRanker";

import { RankerType } from "../structures/inputBenchmarkingModelParams";

export function resolveTheoremsRanker(
    rankerType: RankerType
): ContextTheoremsRanker {
    switch (rankerType) {
        case "distance":
            return new DistanceContextTheoremsRanker();
        case "random":
            return new RandomContextTheoremsRanker();
        case "jaccardIndex":
            return new JaccardIndexContextTheoremsRanker();
    }
}
