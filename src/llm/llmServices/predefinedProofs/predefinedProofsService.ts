import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    ErrorsHandlingMode,
    GeneratedProofImpl,
    ProofVersion,
} from "../llmService";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { PredefinedProofsModelParams } from "../modelParams";
import { Time, timeZero } from "../utils/time";

import { PredefinedProofsModelParamsResolver } from "./predefinedProofsModelParamsResolver";

export class PredefinedProofsService extends LLMServiceImpl<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams,
    PredefinedProofsService,
    PredefinedProof,
    PredefinedProofsServiceInternal
> {
    protected readonly internal: PredefinedProofsServiceInternal;
    protected readonly modelParamsResolver =
        new PredefinedProofsModelParamsResolver();

    constructor(
        eventLogger?: EventLogger,
        debugLogs: boolean = false,
        generationsLogsFilePath?: string
    ) {
        super(
            "PredefinedProofsService",
            eventLogger,
            debugLogs,
            generationsLogsFilePath
        );
        this.internal = new PredefinedProofsServiceInternal(
            this,
            this.eventLoggerGetter,
            this.generationsLoggerBuilder
        );
    }

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: PredefinedProofsModelParams,
        choices: number = params.defaultChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<PredefinedProof[]> {
        return this.internal.logGenerationAndHandleErrors(
            params,
            choices,
            errorsHandlingMode,
            (_request) => {
                LLMServiceInternal.validateChoices(choices);
                const tactics = params.tactics;
                if (choices > tactics.length) {
                    throw new ConfigurationError(
                        `requested ${choices} choices, there are only ${tactics.length} predefined tactics available`
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
            (proof) =>
                this.internal.constructGeneratedProof(
                    proof,
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
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        llmServiceInternal: PredefinedProofsServiceInternal
    ) {
        super(proof, proofGenerationContext, modelParams, llmServiceInternal);
    }

    async fixProof(
        _diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<PredefinedProof[]> {
        this.llmServiceInternal.unsupportedMethod(
            "`PredefinedProof` cannot be fixed",
            this.modelParams,
            choices,
            errorsHandlingMode
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
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        _previousProofVersions?: ProofVersion[]
    ): PredefinedProof {
        return new PredefinedProof(
            proof,
            proofGenerationContext,
            modelParams as PredefinedProofsModelParams,
            this
        );
    }

    generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: PredefinedProofsModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        throw new ConfigurationError(
            "`PredefinedProofsService` does not support generation from chat"
        );
    }
}
