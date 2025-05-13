import { MessageHandler } from "../../../utils/structures/messageHandler";
import { Time, timeZero } from "../../../utils/time";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory } from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { zeroTokens } from "../commonStructures/generationTokens";
import { ProofGenerationMetadataHolder } from "../commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "../commonStructures/proofGenerationType";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceIdentifier } from "../llmServiceIdentifier";
import { LLMServiceInternal } from "../llmServiceInternal";
import { PredefinedProofsModelParams } from "../modelParams";
import { provideBasicSerializer } from "../utils/serialization/basicLLMServiceSerializer";

import { PredefinedProofsModelParamsResolver } from "./predefinedProofsModelParamsResolver";

export class PredefinedProofsService extends LLMServiceImpl<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams,
    PredefinedProofsService,
    PredefinedProof,
    PredefinedProofsServiceInternal
> {
    readonly name = "PredefinedProofsService";
    readonly identifier = LLMServiceIdentifier.PREDEFINED_PROOFS;

    protected readonly internal = new PredefinedProofsServiceInternal(this);
    protected readonly modelParamsResolver =
        new PredefinedProofsModelParamsResolver();
    protected readonly serializer = provideBasicSerializer(this);

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: PredefinedProofsModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        _abortSignal?: AbortSignal,
        onSchedulerDebugLog: MessageHandler = this.internal
            .sendDebugEventOnSchedulerLog
    ): Promise<PredefinedProof[]> {
        return this.internal.scheduleLoggedGenerationAndHandleErrors(
            ProofGenerationType.NO_CHAT,
            params,
            choices,
            metadataHolder,
            onSchedulerDebugLog,
            (_request) => {
                LLMServiceInternal.validateChoices(choices);
                const tactics = params.tactics;
                if (choices > tactics.length) {
                    throw new ConfigurationError(
                        `requested ${choices} choices, but there are only ${tactics.length} predefined tactics available`
                    );
                }
            },
            async (_request) => {
                return {
                    items: this.formatCoqSentences(
                        params.tactics.slice(0, choices)
                    ).map((tactic) => {
                        return {
                            content: `Proof. ${tactic} Qed.`,
                            tokensSpent: zeroTokens(),
                        };
                    }),
                    tokensSpentInTotal: zeroTokens(),
                };
            },
            (rawProof) =>
                this.internal.constructGeneratedProof(
                    rawProof,
                    proofGenerationContext,
                    params
                )
        );
    }

    private formatCoqSentences(commands: string[]): string[] {
        return commands.map((command) => {
            if (command.endsWith(".")) {
                return command;
            } else {
                return command + ".";
            }
        });
    }

    estimateTimeToBecomeAvailable(): Time {
        return timeZero; // predefined proofs are always available
    }
}

export class PredefinedProof extends GeneratedProofImpl<
    PredefinedProofsModelParams,
    PredefinedProofsService,
    PredefinedProof,
    PredefinedProofsServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        llmServiceInternal: PredefinedProofsServiceInternal
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal
        );
    }

    async fixProof(
        _diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices
    ): Promise<PredefinedProof[]> {
        this.llmServiceInternal.unsupportedMethod(
            "`PredefinedProof` cannot be fixed",
            ProofGenerationType.NO_CHAT,
            this.modelParams,
            choices
        );
        return [];
    }

    canBeFixed(): Boolean {
        return false;
    }
}

class PredefinedProofsServiceInternal extends LLMServiceInternal<
    PredefinedProofsModelParams,
    PredefinedProofsService,
    PredefinedProof,
    PredefinedProofsServiceInternal
> {
    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        _previousProofVersions?: ProofVersion[]
    ): PredefinedProof {
        return new PredefinedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this
        );
    }

    // `this.serviceSetup.generationParallelism` is actually unused, yes
    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.llmService.name,
            this.serviceSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: PredefinedProofsModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        this.unsupportedMethod(
            "`PredefinedProofsService` does not support generation from chat",
            ProofGenerationType.NO_CHAT,
            _params,
            _choices
        );
        return {
            items: [],
            tokensSpentInTotal: zeroTokens(),
        };
    }
}
