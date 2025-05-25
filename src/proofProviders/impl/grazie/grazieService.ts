import { ProofGenerationContext } from "../../proofGenerationContext";
import { GrazieUserModelParams } from "../../userModelParams";
import {
    AnalyzedChatHistory,
    ChatHistory,
    ChatMessage,
} from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProof } from "../generatedProof";
import { GrazieModelParams } from "../modelParams";
import { ProofProvider } from "../proofProvider";
import { ProofProviderIdentifier } from "../proofProviderIdentifier";
import { ProofProviderInternal } from "../proofProviderInternal";
import { toO1CompatibleChatHistory } from "../utils/o1ClassModels";
import { provideBasicSerializer } from "../utils/serialization/basicProofProviderSerializer";

import { GrazieApi, GrazieChatRole, GrazieFormattedHistory } from "./grazieApi";
import { GrazieModelParamsResolver } from "./grazieModelParamsResolver";

export class GrazieService extends ProofProvider<
    GrazieUserModelParams,
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
    readonly name = "GrazieService";
    readonly identifier = ProofProviderIdentifier.GRAZIE;

    protected readonly internal = new GrazieServiceInternal(this);
    protected readonly modelParamsResolver = new GrazieModelParamsResolver();
    protected readonly serializer = provideBasicSerializer(this);

    /**
     * As specified in Grazie REST API, `maxTokensToGenerate` is a constant currently.
     */
    static readonly maxTokensToGeneratePredefined = 1024;
}

export class GrazieGeneratedProof extends GeneratedProof<
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: GrazieModelParams,
        proofProviderInternal: GrazieServiceInternal,
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

class GrazieServiceInternal extends ProofProviderInternal<
    GrazieModelParams,
    GrazieService,
    GrazieGeneratedProof,
    GrazieServiceInternal
> {
    readonly api = new GrazieApi(this.logDebug);

    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: GrazieModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GrazieGeneratedProof {
        return new GrazieGeneratedProof(
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
            (params: GrazieModelParams) => params.modelName,
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        analyzedChat: AnalyzedChatHistory,
        params: GrazieModelParams,
        choices: number
    ): Promise<GeneratedRawContent> {
        ProofProviderInternal.validateChoices(choices);
        const completions: Promise<string>[] = [];
        const formattedChat = this.formatChatHistory(analyzedChat.chat, params);

        while (completions.length < choices) {
            completions.push(
                this.api.requestChatCompletion(params, formattedChat)
            );
        }
        const rawContentItems = await Promise.all(completions);

        // TODO: find a way to get actual tokens spent instead of approximation
        return ProofProviderInternal.aggregateToGeneratedRawContent(
            rawContentItems,
            analyzedChat.estimatedTokens.messagesTokens,
            params.modelName
        );
    }

    private formatChatHistory(
        chat: ChatHistory,
        modelParams: GrazieModelParams
    ): GrazieFormattedHistory {
        const o1CompatibleChatHistory = toO1CompatibleChatHistory(
            chat,
            modelParams.modelName,
            "grazie"
        );

        return o1CompatibleChatHistory.map((message: ChatMessage) => {
            const grazieRoleName =
                message.role[0].toUpperCase() + message.role.slice(1);
            return {
                role: grazieRoleName as GrazieChatRole,
                text: message.content,
            };
        });
    }
}
