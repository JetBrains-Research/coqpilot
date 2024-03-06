import { GrazieModelParams } from "../modelParams";
import { GrazieFormattedHistory } from "./grazieApi";

export interface GrazieApiInterface {
    chatCompletionRequest(
        params: GrazieModelParams,
        history: GrazieFormattedHistory
    ): Promise<string>;
}
