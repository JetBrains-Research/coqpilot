import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import {
    PredefinedProofsUserModelParams,
    UserModelParams,
} from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { LLMService } from "../llmService";
import { ModelParams, PredefinedProofsModelParams } from "../modelParams";
import { GenerationRequest } from "../utils/generationsLogger/generationsLogger";
import { Time, timeZero } from "../utils/time";

export class PredefinedProofsService extends LLMService {
    protected readonly internal: PredefinedProofsServiceInternal;

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
        params: ModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<GeneratedProof[]> {
        const predefinedProofsParams = params as PredefinedProofsModelParams;
        return this.internal.logGenerationAndHandleErrors(
            errorsHandlingMode,
            () => {
                if (choices <= 0) {
                    throw new ConfigurationError(
                        `bad choices: ${choices} <= 0`
                    );
                }
                const tactics = predefinedProofsParams.tactics;
                if (choices > tactics.length) {
                    throw new ConfigurationError(
                        `bad choices ${choices}: there are only ${tactics.length} predefined tactics available`
                    );
                }
                return {
                    params: params,
                    choices: choices,
                } as GenerationRequest;
            },
            async (_request) => {
                return this.formatCoqSentences(
                    predefinedProofsParams.tactics.slice(0, choices)
                ).map((tactic) => `Proof. ${tactic} Qed.`);
            },
            (proof) =>
                this.internal.constructGeneratedProof(
                    proof,
                    proofGenerationContext,
                    predefinedProofsParams
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

    resolveParameters(params: UserModelParams): ModelParams {
        const castedParams = params as PredefinedProofsUserModelParams;
        if (castedParams.tactics.length === 0) {
            throw Error(
                "no tactics are selected in the PredefinedProofsModelParams"
            );
        }
        const modelParams: PredefinedProofsModelParams = {
            modelId: params.modelId,
            newMessageMaxTokens: Math.max(
                ...castedParams.tactics.map((tactic) => tactic.length)
            ),
            tokensLimit: Number.POSITIVE_INFINITY,
            systemPrompt: "",
            multiroundProfile: {
                maxRoundsNumber: 1,
                proofFixChoices: 0,
                proofFixPrompt: "",
            },
            tactics: castedParams.tactics,
        };
        return modelParams;
    }
}

export class PredefinedProof extends GeneratedProof {
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
        _choices: number,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<GeneratedProof[]> {
        this.llmServiceInternal.unsupportedMethod(
            "PredefinedProof cannot be fixed",
            errorsHandlingMode
        );
        return [];
    }

    canBeFixed(): Boolean {
        return false;
    }
}

class PredefinedProofsServiceInternal extends LLMServiceInternal {
    constructGeneratedProof(
        proof: string,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        _previousProofVersions?: ProofVersion[]
    ): GeneratedProof {
        return new PredefinedProof(
            proof,
            proofGenerationContext,
            modelParams as PredefinedProofsModelParams,
            this
        );
    }

    generateFromChatImpl(
        _chat: ChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<string[]> {
        throw new ConfigurationError(
            "PredefinedProofsService does not support generation from chat"
        );
    }
}
