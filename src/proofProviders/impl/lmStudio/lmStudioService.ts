import { throwOnAbort } from "../../../utils/async/abortUtils";
import { asErrorOrRethrow } from "../../../utils/errors/errorsUtils";
import { toUnformattedJsonString } from "../../../utils/printers";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { LMStudioUserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory, ChatHistory } from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProof } from "../generatedProof";
import { LMStudioModelParams } from "../modelParams";
import { ProofProvider } from "../proofProvider";
import { ProofProviderIdentifier } from "../proofProviderIdentifier";
import { ProofProviderInternal } from "../proofProviderInternal";
import { provideBasicSerializer } from "../utils/serialization/basicProofProviderSerializer";

import { LMStudioModelParamsResolver } from "./lmStudioModelParamsResolver";

export class LMStudioService extends ProofProvider<
    LMStudioUserModelParams,
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
> {
    readonly name = "LMStudioService";
    readonly identifier = ProofProviderIdentifier.LMSTUDIO;

    protected readonly internal = new LMStudioServiceInternal(this);
    protected readonly modelParamsResolver = new LMStudioModelParamsResolver();
    protected readonly serializer = provideBasicSerializer(this);
}

export class LMStudioGeneratedProof extends GeneratedProof<
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: LMStudioModelParams,
        proofProviderInternal: LMStudioServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal,
            previousProofVersions
        );
    }
}

class LMStudioServiceInternal extends ProofProviderInternal<
    LMStudioModelParams,
    LMStudioService,
    LMStudioGeneratedProof,
    LMStudioServiceInternal
> {
    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: LMStudioModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): LMStudioGeneratedProof {
        return new LMStudioGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.limitParallelismForModelsWithSameKey(
            this.proofProviderSetup.generationParallelism,
            (params: LMStudioModelParams) => params.port,
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: LMStudioModelParams,
        choices: number,
        abortSignal?: AbortSignal
    ): Promise<GeneratedRawContent> {
        ProofProviderInternal.validateChoices(choices);
        let attempts = choices * 2;
        const completions: string[] = [];
        this.logDebug.event("Completion requested", {
            history: analyzedChat.chat,
        });

        let lastErrorThrown: Error | undefined = undefined;
        while (completions.length < choices && attempts > 0) {
            try {
                throwOnAbort(abortSignal);
                const responce = await fetch(this.endpoint(params), {
                    method: "POST",
                    headers: this.headers,
                    body: this.body(analyzedChat.chat, params),
                });
                if (responce.ok) {
                    const res = await responce.json();
                    const newCompletion = res.choices[0].message.content;
                    completions.push(newCompletion);
                    this.logDebug.event("Completion succeeded", {
                        newCompletion: newCompletion,
                    });
                }
            } catch (err) {
                this.logDebug.event("Completion failed", {
                    error: err,
                });
                lastErrorThrown = asErrorOrRethrow(err);
            }
            attempts--;
        }
        if (completions.length < choices) {
            throw lastErrorThrown;
        }

        // TODO: find a way to get actual tokens spent instead of approximation
        return ProofProviderInternal.aggregateToGeneratedRawContent(
            completions,
            analyzedChat.estimatedTokens.messagesTokens,
            undefined
        );
    }

    private readonly headers = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "Content-Type": "application/json",
    };

    private body(messages: ChatHistory, params: LMStudioModelParams): string {
        return toUnformattedJsonString({
            messages: messages,
            stream: false,
            temperature: params.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: params.maxTokensToGenerate,
        });
    }

    private endpoint(params: LMStudioModelParams): string {
        return `http://localhost:${params.port}/v1/chat/completions`;
    }
}
