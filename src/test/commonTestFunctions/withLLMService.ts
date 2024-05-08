import { LLMService } from "../../llm/llmServices/llmService";
import { ModelParams } from "../../llm/llmServices/modelParams";
import { UserModelParams } from "../../llm/userModelParams";

export async function withLLMService<S extends LLMService, R>(
    llmService: S,
    block: (llmService: S) => Promise<R>
): Promise<R> {
    try {
        return await block(llmService);
    } finally {
        llmService.dispose();
    }
}

export async function withLLMServiceAndParams<
    S extends LLMService,
    P extends ModelParams,
    R,
>(
    llmService: S,
    userParams: UserModelParams,
    block: (llmService: S, params: P) => Promise<R>
): Promise<R> {
    try {
        const params = llmService.resolveParameters(userParams) as P;
        return await block(llmService, params);
    } finally {
        llmService.dispose();
    }
}
