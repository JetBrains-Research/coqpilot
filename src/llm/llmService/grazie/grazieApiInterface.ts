import { GrazieRequestParams } from "../serviceParams";

export interface GrazieApiInterface {
    chatCompletionRequest(params: GrazieRequestParams): Promise<string>;
}