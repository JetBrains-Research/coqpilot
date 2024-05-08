import { LLMService } from "../../llm/llmServices/llmService";
import { ModelParams } from "../../llm/llmServices/modelParams";
import { UserModelParams } from "../../llm/userModelParams";

export function withLLMService<S extends LLMService, R>(
    llmService: S,
    block: (llmService: S) => R
): R {
    try {
        return block(llmService);
    } finally {
        llmService.dispose();
    }
}

export function withLLMServiceAndParams<
    S extends LLMService,
    P extends ModelParams,
    R,
>(
    llmService: S,
    userParams: UserModelParams,
    block: (llmService: S, params: P) => R
): R {
    try {
        const params = llmService.resolveParameters(userParams) as P;
        return block(llmService, params);
    } finally {
        llmService.dispose();
    }
}
