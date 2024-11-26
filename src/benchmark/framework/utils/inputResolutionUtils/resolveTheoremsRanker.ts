import { DistanceContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/distanceContextTheoremsRanker";
import { JaccardIndexContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/jaccardIndexContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/randomContextTheoremsRanker";
import { ContextTheoremsRanker } from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

import { RankerType } from "../../structures/inputParameters/inputBenchmarkingModelParams";

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
