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
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { PredefinedProofsModelParams } from "../modelParams";

import { PredefinedProofsModelParamsResolver } from "./predefinedProofsModelParamsResolver";

export class PredefinedProofsService extends LLMServiceImpl<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams,
    PredefinedProofsService,
    PredefinedProof,
    PredefinedProofsServiceInternal
> {
    readonly serviceName = "PredefinedProofsService";
    protected readonly internal = new PredefinedProofsServiceInternal(
        this,
        this.eventLogger,
        this.generationsLoggerBuilder
    );
    protected readonly modelParamsResolver =
        new PredefinedProofsModelParamsResolver();

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: PredefinedProofsModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined
    ): Promise<PredefinedProof[]> {
        return this.internal.logGenerationAndHandleErrors(
            ProofGenerationType.NO_CHAT,
            params,
            choices,
            metadataHolder,
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
