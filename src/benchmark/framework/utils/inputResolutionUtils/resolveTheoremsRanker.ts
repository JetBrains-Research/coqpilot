import { DistanceContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/distanceContextTheoremsRanker";
import { EuclidContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/euclidContextTheoremRanker";
import { JaccardIndexContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/jaccardIndexContextTheoremsRanker";
import { RandomContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/randomContextTheoremsRanker";
import { WeightedJaccardIndexContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/weightedJaccardIndexTheoremRanker";
import { CosineContextTheoremsRanker } from "../../../../core/contextTheoremRanker/actualRankers/сosineContextTheoremRanker";
import {
    ContextTheoremsRanker,
    RankerType,
} from "../../../../core/contextTheoremRanker/contextTheoremsRanker";

export function resolveTheoremsRanker(
    rankerType: RankerType
): ContextTheoremsRanker {
    switch (rankerType) {
        case "distance":
            return new DistanceContextTheoremsRanker();
        case "euclid":
            return new EuclidContextTheoremsRanker();
        case "jaccardIndex":
            return new JaccardIndexContextTheoremsRanker();
        case "random":
            return new RandomContextTheoremsRanker();
        case "weightedJaccardIndex":
            return new WeightedJaccardIndexContextTheoremsRanker();
        case "cosine":
            return new CosineContextTheoremsRanker();
    }
}
