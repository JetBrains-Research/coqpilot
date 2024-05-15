import { Result } from "ts-results";

export interface ApiGoal {
    hypothesis: string[];
    conclusion: string;
}

export type CheckProofResult = Result<ApiGoal | undefined, string>;
