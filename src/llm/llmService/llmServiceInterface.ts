import {
    CompletionContext,
    ModelParams
} from "./modelParamsInterfaces";

export type LlmServiceId = string;

export interface LLMServiceInterface {
    requestCompletion(completionContext: CompletionContext, params: ModelParams): Promise<string[]>;

    dispose(): void;
}