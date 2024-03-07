import * as assert from "assert";

import { EventLogger } from "../../logging/eventLogger";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { ChatHistory } from "./chat";
import { ModelParams, MultiroundProfile } from "./modelParams";
import {
    buildProofFixChat,
    buildProofGenerationChat,
} from "./utils/chatFactory";

export type Proof = string;

export interface ProofVersion {
    proof: Proof;
    diagnostic?: string;
}

export abstract class LLMService {
    constructor(protected readonly eventLogger?: EventLogger) {}

    abstract constructGeneratedProof(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[]
    ): GeneratedProof;

    abstract generateFromChat(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]>;

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams,
        choices: number
    ): Promise<GeneratedProof[]> {
        if (choices <= 0) {
            return [];
        }
        const chat = buildProofGenerationChat(proofGenerationContext, params);
        const proofs = await this.generateFromChat(chat, params, choices);
        return proofs.map((proof: string) =>
            this.constructGeneratedProof(proof, proofGenerationContext, params)
        );
    }

    dispose(): void {}

    resolveParameters(params: UserModelParams): ModelParams {
        return this.resolveParametersWithDefaults(params);
    }

    protected readonly resolveParametersWithDefaults = (
        params: UserModelParams
    ): ModelParams => {
        const newMessageMaxTokens =
            params.newMessageMaxTokens ??
            this.defaultNewMessageMaxTokens[params.modelName];
        const tokensLimits =
            params.tokensLimit ?? this.defaultTokensLimits[params.modelName];
        const systemMessageContent =
            params.systemPrompt ?? this.defaultSystemMessageContent;
        const multiroundProfile: MultiroundProfile = {
            maxRoundsNumber:
                params.multiroundProfile?.maxRoundsNumber ??
                this.defaultMultiroundProfile.maxRoundsNumber,
            proofFixChoices:
                params.multiroundProfile?.proofFixChoices ??
                this.defaultMultiroundProfile.proofFixChoices,
            proofFixPrompt:
                params.multiroundProfile?.proofFixPrompt ??
                this.defaultMultiroundProfile.proofFixPrompt,
        };
        if (newMessageMaxTokens === undefined || tokensLimits === undefined) {
            throw Error(`user model parameters cannot be resolved: ${params}`);
        }
        return {
            modelName: params.modelName,
            systemPrompt: systemMessageContent,
            newMessageMaxTokens: newMessageMaxTokens,
            tokensLimit: tokensLimits,
            multiroundProfile: multiroundProfile,
        };
    };

    private readonly defaultTokensLimits: {
        [modelName: string]: number;
    } = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "gpt-3.5-turbo-0301": 2000,
    };

    private readonly defaultNewMessageMaxTokens: {
        [modelName: string]: number;
    } = {};

    private readonly defaultSystemMessageContent: string =
        "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";

    // its properties can be used separately
    private readonly defaultMultiroundProfile: MultiroundProfile = {
        maxRoundsNumber: 1, // multiround is disabled by default
        proofFixChoices: 1, // 1 fix version per proof by default
        proofFixPrompt:
            "Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.",
    };
}

export abstract class GeneratedProof {
    readonly llmService: LLMService;
    readonly modelParams: ModelParams;
    readonly maxRoundsNumber: number;

    readonly proofGenerationContext: ProofGenerationContext;
    readonly proofVersions: ProofVersion[];

    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        llmService: LLMService,
        previousProofVersions?: ProofVersion[]
    ) {
        this.llmService = llmService;
        this.modelParams = modelParams;

        this.proofGenerationContext = proofGenerationContext;
        this.proofVersions = previousProofVersions ?? [];
        this.proofVersions.push({
            proof: proof,
            diagnostic: undefined,
        });

        this.maxRoundsNumber =
            this.modelParams.multiroundProfile.maxRoundsNumber;
        if (this.maxRoundsNumber < this.proofVersions.length) {
            throw new Error(
                `proof cannot be generated: max rounds number (${this.maxRoundsNumber}) was already reached`
            );
        }
    }

    private lastProofVersion(): ProofVersion {
        return this.proofVersions[this.proofVersions.length - 1];
    }

    proof(): Proof {
        return this.lastProofVersion().proof;
    }

    // starts with zero, then +1 for each version
    versionNumber(): number {
        return this.proofVersions.length - 1;
    }

    protected async generateNextVersion(
        chat: ChatHistory,
        choices: number
    ): Promise<GeneratedProof[]> {
        if (!this.nextVersionCanBeGenerated() || choices <= 0) {
            return [];
        }
        const newProofs = await this.llmService.generateFromChat(
            chat,
            this.modelParams,
            choices
        );
        return newProofs.map((proof: string) =>
            this.llmService.constructGeneratedProof(
                proof,
                this.proofGenerationContext,
                this.modelParams,
                this.proofVersions
            )
        );
    }

    /**
     * `modelParams.multiroundProfile.fixedProofChoices` can be overriden here
     * with `choices` parameter
     */
    async fixProof(
        diagnostic: string,
        choices: number = this.modelParams.multiroundProfile.proofFixChoices
    ): Promise<GeneratedProof[]> {
        if (choices <= 0 || !this.canBeFixed()) {
            return [];
        }

        const lastProofVersion = this.lastProofVersion();
        assert.ok(lastProofVersion.diagnostic === undefined);
        lastProofVersion.diagnostic = diagnostic;

        const chat = buildProofFixChat(
            this.proofGenerationContext,
            this.proofVersions,
            this.modelParams
        );
        return this.generateNextVersion(chat, choices);
    }

    protected nextVersionCanBeGenerated(): Boolean {
        return this.versionNumber() < this.maxRoundsNumber;
    }

    // doesn't check this.modelParams.multiroundProfile.fixedProofChoices, because they can be overriden
    canBeFixed(): Boolean {
        return this.nextVersionCanBeGenerated();
    }
}
