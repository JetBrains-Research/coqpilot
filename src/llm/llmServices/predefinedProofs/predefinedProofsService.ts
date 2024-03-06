import { EventLogger } from "../../../logging/eventLogger";
import { ProofGenerationContext } from "../../proofGenerationContext";
import {
    PredefinedProofsUserModelParams,
    UserModelParams,
} from "../../userModelParams";
import { ChatHistory } from "../chat";
import { GeneratedProof, Proof, ProofVersion } from "../llmService";
import { LLMService } from "../llmService";
import { ModelParams, PredefinedProofsModelParams } from "../modelParams";

export class PredefinedProofsService extends LLMService {
    constructor(eventLogger?: EventLogger) {
        super(eventLogger);
    }

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

    generateFromChat(
        _chat: ChatHistory,
        _params: ModelParams,
        _choices: number
    ): Promise<string[]> {
        throw new Error(
            "PredefinedProofsService does not support generation from chat"
        );
    }

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams,
        choices: number
    ): Promise<GeneratedProof[]> {
        const predefinedProofsParams = params as PredefinedProofsModelParams;
        const tactics = predefinedProofsParams.tactics;
        if (choices > tactics.length) {
            throw Error(
                `invalid choices ${choices}: there are only ${tactics.length} predefined tactics available`
            );
        }
        return this.formatCoqSentences(tactics.slice(0, choices)).map(
            (tactic) =>
                new PredefinedProof(
                    `Proof. ${tactic} Qed.`,
                    proofGenerationContext,
                    predefinedProofsParams,
                    this
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

    resolveParameters(params: UserModelParams): ModelParams {
        const castedParams = params as PredefinedProofsUserModelParams;
        if (castedParams.tactics.length === 0) {
            throw Error(
                "no tactics are selected in the PredefinedProofsModelParams"
            );
        }
        return {
            modelName: params.modelName,
            newMessageMaxTokens: Math.max(
                ...castedParams.tactics.map((tactic) => tactic.length)
            ),
            tokensLimit: Number.POSITIVE_INFINITY,
            systemPromt: "",
        };
    }
}

export class PredefinedProof extends GeneratedProof {
    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: PredefinedProofsModelParams,
        llmService: PredefinedProofsService
    ) {
        super(proof, proofGenerationContext, modelParams, llmService);
    }

    protected generateNextVersion(
        _chat: ChatHistory,
        _choices: number
    ): Promise<GeneratedProof[]> {
        throw new Error(
            "PredefinedProof does not support next version generation"
        );
    }

    fixProof(_diagnostic: string, _choices: number): Promise<GeneratedProof[]> {
        throw new Error("PredefinedProof cannot be fixed");
    }
}
