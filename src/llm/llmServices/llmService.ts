import { Theorem } from "../../coqParser/parsedTypes";
import { EventLogger } from "../../logging/eventLogger";
import { ChatHistory } from "./chat";
import { buildFixProofChat, buildGenerateProofChat } from "./chatFactory";
import { ModelParams } from "./modelParams";
import { UserModelParams } from "./userModelParams";
import * as assert from "assert";

export type Proof = string;

export interface ProofVersion {
    proof: Proof;
    diagnostic?: string;
}

export interface ProofGenerationContext {
    completionTarget: string;
    contextTheorems: Theorem[];
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
        const chat = buildGenerateProofChat(proofGenerationContext, params);
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
            params.systemPromt ?? this.defaultSystemMessageContent;
        if (
            newMessageMaxTokens === undefined ||
            tokensLimits === undefined ||
            systemMessageContent === undefined
        ) {
            throw Error(`user model parameters cannot be resolved: ${params}`);
        }
        return {
            modelName: params.modelName,
            systemPromt: systemMessageContent,
            newMessageMaxTokens: newMessageMaxTokens,
            tokensLimit: tokensLimits,
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

    private readonly defaultSystemMessageContent =
        "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";
}

// TODO 2: implement interfaces in services
// TODO 3: implement in core logic
// TODO 4: support params, refactor Grazie
// TODO 5: test
// TODO 6: docs

export abstract class GeneratedProof {
    readonly llmService: LLMService;
    readonly modelParams: ModelParams;

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
    }

    private lastProofVersion(): ProofVersion {
        return this.proofVersions[this.proofVersions.length - 1];
    }

    proof(): Proof {
        return this.lastProofVersion().proof;
    }

    protected async generateNextVersion(
        chat: ChatHistory,
        choices: number
    ): Promise<GeneratedProof[]> {
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

    async fixProof(
        diagnostic: string,
        choices: number
    ): Promise<GeneratedProof[]> {
        const lastProofVersion = this.lastProofVersion();
        assert.ok(lastProofVersion.diagnostic === undefined);
        lastProofVersion.diagnostic = diagnostic;

        const chat = buildFixProofChat(
            this.proofGenerationContext,
            this.proofVersions,
            this.modelParams
        );
        return this.generateNextVersion(chat, choices);
    }
}
