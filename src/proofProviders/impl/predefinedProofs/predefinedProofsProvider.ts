import { MessageHandler } from "../../../utils/structures/messageHandler";
import { Time, timeZero } from "../../../utils/time";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { ConfigurationError } from "../../proofProviderErrors";
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
import { GeneratedProof } from "../generatedProof";
import { PredefinedProofsModelParams } from "../modelParams";
import { ProofProvider } from "../proofProvider";
import { ProofProviderIdentifier } from "../proofProviderIdentifier";
import { ProofProviderInternal } from "../proofProviderInternal";
import { provideBasicSerializer } from "../utils/serialization/basicProofProviderSerializer";

import { PredefinedProofsModelParamsResolver } from "./predefinedProofsModelParamsResolver";

export class PredefinedProofsProvider extends ProofProvider<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams,
    PredefinedProofsProvider,
    PredefinedProof,
    PredefinedProofsProviderInternal
> {
    readonly name = "PredefinedProofsProvider";
    readonly identifier = ProofProviderIdentifier.PREDEFINED_PROOFS;

    protected readonly internal = new PredefinedProofsProviderInternal(this);
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
                ProofProviderInternal.validateChoices(choices);
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

export class PredefinedProof extends GeneratedProof<
    PredefinedProofsModelParams,
    PredefinedProofsProvider,
    PredefinedProof,
    PredefinedProofsProviderInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        proofProviderInternal: PredefinedProofsProviderInternal
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal
        );
    }

    async fixProof(
        _diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices
    ): Promise<PredefinedProof[]> {
        this.proofProviderInternal.unsupportedMethod(
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

class PredefinedProofsProviderInternal extends ProofProviderInternal<
    PredefinedProofsModelParams,
    PredefinedProofsProvider,
    PredefinedProof,
    PredefinedProofsProviderInternal
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

    // `this.proofProviderSetup.generationParallelism` is actually unused, yes
    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
        );

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: PredefinedProofsModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        this.unsupportedMethod(
            "`PredefinedProofsProvider` does not support generation from chat",
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
