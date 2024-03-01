import { Theorem } from "../../coqParser/parsedTypes";
import { ChatHistory } from "./chat";
import { buildFixProofChat } from "./chatFactory";
import { ModelParams } from "./modelParams";
import * as assert from "assert";

export type Proof = string;
export type ProofBatch = Proof[];

export interface ProofWithDiagnostic {
    proof: Proof;
    diagnostic?: string;
}

export interface ProofGenerationContext {
    completionTarget: string;
    contextTheorems: Theorem[];
}

export abstract class LLMService {
    abstract generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams
    ): Promise<GeneratedProof[]>;

    abstract generateFromChat(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): string[];

    abstract dispose(): void;
}

// TODO 1: refactor interfaces to support making shorter / etc requests
// TODO 2: implement interfaces in services
// TODO 3: implement in core logic
// TODO 4: support params
// TODO 5: test
// TODO 6: docs

export abstract class GeneratedProof {
    readonly llmService: LLMService;
    readonly modelParams: ModelParams;

    readonly proofGenerationContext: ProofGenerationContext;
    readonly proofVersions: ProofWithDiagnostic[];

    readonly systemMessageContent: string | undefined;

    constructor(
        llmService: LLMService,
        modelParams: ModelParams,
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        systemMessageContent?: string,
        previousProofVersions?: ProofWithDiagnostic[]
    ) {
        this.llmService = llmService;
        this.modelParams = modelParams;

        this.proofGenerationContext = proofGenerationContext;
        this.proofVersions = previousProofVersions ?? [];
        this.proofVersions.push({
            proof: proof,
            diagnostic: undefined,
        });
        this.systemMessageContent = systemMessageContent;
    }

    private lastProofVersion(): ProofWithDiagnostic {
        return this.proofVersions[this.proofVersions.length - 1];
    }

    proof(): Proof {
        return this.lastProofVersion().proof;
    }

    async fixProof(
        diagnostic: string,
        choices: number
    ): Promise<GeneratedProof[]> {
        const lastProofVersion = this.lastProofVersion();
        assert.ok(lastProofVersion.diagnostic === undefined);
        lastProofVersion.diagnostic = diagnostic;

        return this.generateFixedProof(choices);
    }

    protected async generateFixedProof(
        choices: number
    ): Promise<GeneratedProof[]> {
        const chat = buildFixProofChat(
            this.modelParams,
            this.proofGenerationContext,
            this.proofVersions,
            this.systemMessageContent
        );
        const newProofs = this.llmService.generateFromChat(
            chat,
            this.modelParams,
            choices
        );
        return newProofs.map(this.constructNextGeneratedProof);
    }

    protected abstract constructNextGeneratedProof(
        proof: string
    ): GeneratedProof;
}
