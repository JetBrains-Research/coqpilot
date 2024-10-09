import { LLMService } from "../../llm/llmServices/llmService";
import { ModelParams } from "../../llm/llmServices/modelParams";
import { resolveParametersOrThrow } from "../../llm/llmServices/utils/resolveOrThrow";
import { UserModelParams } from "../../llm/userModelParams";

export async function withLLMService<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<InputModelParams, ResolvedModelParams>,
    T,
>(
    llmService: LLMServiceType,
    block: (llmService: LLMServiceType) => Promise<T>
): Promise<T> {
    try {
        return await block(llmService);
    } finally {
        llmService.dispose();
    }
}

export async function withLLMServiceAndParams<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends LLMService<InputModelParams, ResolvedModelParams>,
    T,
>(
    llmService: LLMServiceType,
    inputParams: InputModelParams,
    block: (
        llmService: LLMServiceType,
        resolvedParams: ResolvedModelParams
    ) => Promise<T>
): Promise<T> {
    try {
        const resolvedParams = resolveParametersOrThrow(
            llmService,
            inputParams
        );
        return await block(llmService, resolvedParams);
    } finally {
        llmService.dispose();
    }
}
