import * as assert from "assert";

import { EventLogger } from "../../logging/eventLogger";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory, ChatHistory } from "./chat";
import { ModelParams, MultiroundProfile } from "./modelParams";
import {
    buildProofFixChat,
    buildProofGenerationChat,
} from "./utils/chatFactory";
import {
    FromChatGenerationRequest,
    RequestsLogger,
} from "./utils/requestsLogger/requestsLogger";

export type Proof = string;

export interface ProofVersion {
    proof: Proof;
    diagnostic?: string;
}

/* eslint-disable @typescript-eslint/naming-convention */
export enum ErrorsHandlingMode {
    LOG_EVENTS_AND_SWALLOW_ERRORS,
    RETHROW_ERRORS,
}

export abstract class LLMService {
    protected readonly requestsLogger: RequestsLogger;

    constructor(
        public readonly serviceName: string,
        requestsLogsFilePath: string,
        protected readonly eventLogger?: EventLogger
    ) {
        this.requestsLogger = new RequestsLogger(requestsLogsFilePath);
    }

    static readonly generationFromChatFailedEvent = `generation-from-chat-failed`;
    static readonly generationFromChatSucceededEvent = `generation-from-chat-succeeded`;

    abstract constructGeneratedProof(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        previousProofVersions?: ProofVersion[]
    ): GeneratedProof;

    /*
     * This method should be only a pure implementation of
     * the generation from chat, namely, its happy path.
     * In case something goes wrong, it should just throw an `Error`.
     */
    protected abstract generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]>;

    /*
     * Unlike the unsafe version, this method handles the errors.
     * Namely, the default implementation catches an error,
     * then logs the corresponding event and, finally,
     * rethrows the wrapped error further if needed.
     * Also, the provided implementation logs all the generation requests
     * (both successful and failed ones) via the `RequestsLogger`:
     * it is needed for the further estimation of the service availability.
     */
    async generateFromChat(
        analyzedChat: AnalyzedChatHistory,
        params: ModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
    ): Promise<string[]> {
        return this.logRequestsAndHandleErrors(
            {
                chat: analyzedChat.chat,
                estimatedTokens: analyzedChat.estimatedTokens,
                params: params,
                choices: choices,
            },
            async () =>
                await this.generateFromChatImpl(
                    analyzedChat.chat,
                    params,
                    choices
                ),
            () => [],
            errorsHandlingMode
        );
    }

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams,
        choices: number
    ): Promise<GeneratedProof[]> {
        if (choices <= 0) {
            return [];
        }
        const analyzedChat = buildProofGenerationChat(
            proofGenerationContext,
            params
        );
        const proofs = await this.generateFromChat(
            analyzedChat,
            params,
            choices
        );
        return proofs.map((proof: string) =>
            this.constructGeneratedProof(proof, proofGenerationContext, params)
        );
    }

    dispose(): void {
        this.requestsLogger.dispose();
    }

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

        /** NOTE: it's important to pass `...params` first
         * because if so, then the omitted fields of the `params`
         * (`systemPromt`, `newMessageMaxTokens`, `tokensLimit`, etc)
         * will be overriden - and not in the opposite way!
         */
        return {
            ...params,
            systemPrompt: systemMessageContent,
            newMessageMaxTokens: newMessageMaxTokens,
            tokensLimit: tokensLimits,
            multiroundProfile: multiroundProfile,
        };
    };

    private readonly defaultNewMessageMaxTokens: {
        [modelName: string]: number;
    } = {};

    private readonly defaultTokensLimits: {
        [modelName: string]: number;
    } = {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "gpt-3.5-turbo-0301": 2000,
    };

    private readonly defaultSystemMessageContent: string =
        "Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.";

    // its properties can be used separately
    private readonly defaultMultiroundProfile: MultiroundProfile = {
        maxRoundsNumber: 1, // multiround is disabled by default
        proofFixChoices: 1, // 1 fix version per proof by default
        proofFixPrompt:
            "Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.",
    };

    protected async logRequestsAndHandleErrors(
        request: FromChatGenerationRequest,
        generateProofs: () => Promise<string[]>,
        returnOnError: () => string[],
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<string[]> {
        try {
            const proofs = await generateProofs();
            this.requestsLogger.logRequestSucceeded(request, proofs);
            this.eventLogger?.logLogicEvent(
                LLMService.generationFromChatSucceededEvent,
                this
            );
            return proofs;
        } catch (e) {
            const error = e as Error;
            if (error === null) {
                throw e;
            }
            this.requestsLogger.logRequestFailed(request, error);
            const serviceError = new GenerationFromChatFailed(error);
            switch (+errorsHandlingMode) {
                case ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS:
                    if (!this.eventLogger) {
                        throw Error(
                            "cannot log events: no `eventLogger` provided"
                        );
                    }
                    this.eventLogger.logLogicEvent(
                        LLMService.generationFromChatFailedEvent,
                        this
                    );
                    return returnOnError();
                case ErrorsHandlingMode.RETHROW_ERRORS:
                    throw serviceError;
                default:
                    throw Error(
                        `unsupported \`ErrorsHandlingMode\`: ${errorsHandlingMode}`
                    );
            }
        }
    }
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
        // Makes a copy of the previous proof versions
        this.proofVersions = [...(previousProofVersions ?? [])];
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

    // starts with one, then +1 for each version
    versionNumber(): number {
        return this.proofVersions.length;
    }

    protected async generateNextVersion(
        analyzedChat: AnalyzedChatHistory,
        choices: number,
        postprocessProof: (proof: string) => string = (proof) => proof
    ): Promise<GeneratedProof[]> {
        if (!this.nextVersionCanBeGenerated() || choices <= 0) {
            return [];
        }
        const newProofs = await this.llmService.generateFromChat(
            analyzedChat,
            this.modelParams,
            choices
        );
        return newProofs.map((proof: string) =>
            this.llmService.constructGeneratedProof(
                postprocessProof(proof),
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

        const analyzedChat = buildProofFixChat(
            this.proofGenerationContext,
            this.proofVersions,
            this.modelParams
        );

        return this.generateNextVersion(
            analyzedChat,
            choices,
            this.parseFixedProofFromMessage.bind(this)
        );
    }

    parseFixedProofFromMessage(message: string): string {
        const regex = /Proof\.(.*?)Qed\./s;
        const match = regex.exec(message);
        if (match) {
            return match[0];
        } else {
            return message;
        }
    }

    protected nextVersionCanBeGenerated(): Boolean {
        return this.versionNumber() < this.maxRoundsNumber;
    }

    // doesn't check this.modelParams.multiroundProfile.fixedProofChoices, because they can be overriden
    canBeFixed(): Boolean {
        return this.nextVersionCanBeGenerated();
    }
}
