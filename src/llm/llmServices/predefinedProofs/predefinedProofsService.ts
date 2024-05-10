import { EventLogger } from "../../../logging/eventLogger";
import { ConfigurationError } from "../../llmServiceErrors";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { PredefinedProofsUserModelParams } from "../../userModelParams";
import { ChatHistory } from "../chat";
import {
    ErrorsHandlingMode,
    GeneratedProof,
    LLMServiceInternal,
    ProofVersion,
} from "../llmService";
import { LLMService } from "../llmService";
import { PredefinedProofsModelParams } from "../modelParams";
import { PredefinedProofsModelParamsResolver } from "../modelParamsResolvers";
import { Time, timeZero } from "../utils/time";

export class PredefinedProofsService extends LLMService<
    PredefinedProofsUserModelParams,
    PredefinedProofsModelParams
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
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<PredefinedProof[]> {
        return this.internal.logGenerationAndHandleErrors(
            params,
            choices,
            errorsHandlingMode,
            (_request) => {
                this.internal.validateChoices(choices);
                const tactics = params.tactics;
                if (tactics.length === 0) {
                    throw new ConfigurationError(
                        "zero predefined tactics specified"
                    );
                }
                if (choices > tactics.length) {
                    throw new ConfigurationError(
                        `requested ${choices} choices, there are only ${tactics.length} predefined tactics available`
                    );
                }
            },
            async (_request) => {
                return this.formatCoqSentences(
                    params.tactics.slice(0, choices)
                ).map((tactic) => `Proof. ${tactic} Qed.`);
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

export class PredefinedProof extends GeneratedProof<PredefinedProofsModelParams> {
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
        choices: number,
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

class PredefinedProofsServiceInternal extends LLMServiceInternal<PredefinedProofsModelParams> {
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
        _chat: ChatHistory,
        _params: PredefinedProofsModelParams,
        _choices: number
    ): Promise<string[]> {
        throw new ConfigurationError(
            "`PredefinedProofsService` does not support generation from chat"
        );
    }
}
