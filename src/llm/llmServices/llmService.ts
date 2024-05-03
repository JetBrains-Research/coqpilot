import * as assert from "assert";
import * as tmp from "tmp";

import { EventLogger } from "../../logging/eventLogger";
import {
    GenerationFromChatFailedError,
    LLMServiceError,
} from "../llmServiceErrors";
import { ProofGenerationContext } from "../proofGenerationContext";
import { UserModelParams } from "../userModelParams";

import { AnalyzedChatHistory, ChatHistory } from "./chat";
import { ModelParams } from "./modelParams";
import {
    buildProofFixChat,
    buildProofGenerationChat,
} from "./utils/chatFactory";
import { estimateTimeToBecomeAvailableDefault } from "./utils/defaultAvailabilityEstimator";
import { resolveParametersWithDefaultsImpl } from "./utils/defaultParametersResolver";
import { LoggerRecord } from "./utils/requestsLogger/loggerRecord";
import {
    FromChatGenerationRequest,
    GenerationRequest,
    RequestsLogger,
} from "./utils/requestsLogger/requestsLogger";
import { Time } from "./utils/time";

export type Proof = string;

export interface ProofVersion {
    proof: Proof;
    diagnostic?: string;
}

/* eslint-disable @typescript-eslint/naming-convention */
export enum ErrorsHandlingMode {
    LOG_EVENTS_AND_SWALLOW_ERRORS = "log events & swallow errors",
    RETHROW_ERRORS = "rethrow errors",
}

export abstract class LLMService {
    protected abstract readonly internal: LLMServiceInternal;
    protected readonly eventLoggerGetter: () => EventLogger | undefined;
    protected readonly requestsLoggerBuilder: () => RequestsLogger;

    constructor(
        readonly serviceName: string,
        eventLogger: EventLogger | undefined,
        debug: boolean,
        requestsLogsFilePath: string | undefined
    ) {
        this.eventLoggerGetter = () => eventLogger;
        this.requestsLoggerBuilder = () =>
            new RequestsLogger(
                requestsLogsFilePath ?? tmp.fileSync().name,
                debug
            );
    }

    static readonly generationFailedEvent = `generation-failed`;
    static readonly generationSucceededEvent = `generation-succeeded`;

    /*
     * Unlike the internal version, this method handles the errors.
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
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<string[]> {
        return this.internal.logRequestsAndHandleErrors(
            {
                chat: analyzedChat.chat,
                estimatedTokens: analyzedChat.estimatedTokens,
                params: params,
                choices: choices,
            } as FromChatGenerationRequest,
            async () =>
                await this.internal.generateFromChatImpl(
                    analyzedChat.chat,
                    params,
                    choices
                ),
            (error) => new GenerationFromChatFailedError(error),
            errorsHandlingMode
        );
    }

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ModelParams,
        choices: number,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
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
            choices,
            errorsHandlingMode
        );
        return proofs.map((proof: string) =>
            this.internal.constructGeneratedProof(
                proof,
                proofGenerationContext,
                params
            )
        );
    }

    /**
     * Estimates the expected time for service to become available.
     * To do this, analyzes the logs from `this.requestsLogger` and computes the time.
     */
    estimateTimeToBecomeAvailable(): Time {
        return estimateTimeToBecomeAvailableDefault(
            this.internal.requestsLogger.readLogsSinceLastSuccess()
        );
    }

    readRequestsLogs(sinceLastSuccess: boolean = false): LoggerRecord[] {
        return sinceLastSuccess
            ? this.internal.requestsLogger.readLogsSinceLastSuccess()
            : this.internal.requestsLogger.readLogs();
    }

    dispose(): void {
        this.internal.dispose();
    }

    resolveParameters(params: UserModelParams): ModelParams {
        return this.resolveParametersWithDefaults(params);
    }

    protected readonly resolveParametersWithDefaults = (
        params: UserModelParams
    ): ModelParams => resolveParametersWithDefaultsImpl(params);
}

export abstract class LLMServiceInternal {
    readonly eventLogger: EventLogger | undefined;
    readonly requestsLogger: RequestsLogger;

    constructor(
        readonly llmService: LLMService,
        eventLoggerGetter: () => EventLogger | undefined,
        requestsLoggerBuilder: () => RequestsLogger
    ) {
        this.eventLogger = eventLoggerGetter();
        this.requestsLogger = requestsLoggerBuilder();
    }

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
    abstract generateFromChatImpl(
        chat: ChatHistory,
        params: ModelParams,
        choices: number
    ): Promise<string[]>;

    async logRequestsAndHandleErrors(
        request: GenerationRequest,
        generateProofs: () => Promise<string[]>,
        wrapError: (error: Error) => LLMServiceError,
        errorsHandlingMode: ErrorsHandlingMode
    ): Promise<string[]> {
        try {
            const proofs = await generateProofs();
            this.requestsLogger.logRequestSucceeded(request, proofs);
            this.eventLogger?.logLogicEvent(
                LLMService.generationSucceededEvent,
                this.llmService
            );
            return proofs;
        } catch (e) {
            const error = e as Error;
            if (error === null) {
                throw e;
            }
            this.requestsLogger.logRequestFailed(request, error);
            const serviceError = wrapError(error);
            switch (errorsHandlingMode) {
                case ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS:
                    if (!this.eventLogger) {
                        throw Error(
                            "cannot log events: no `eventLogger` provided"
                        );
                    }
                    this.eventLogger.logLogicEvent(
                        LLMService.generationFailedEvent,
                        this.llmService
                    );
                    return [];
                case ErrorsHandlingMode.RETHROW_ERRORS:
                    throw serviceError;
                default:
                    throw Error(
                        `unsupported \`ErrorsHandlingMode\`: ${errorsHandlingMode}`
                    );
            }
        }
    }

    dispose(): void {
        this.requestsLogger.dispose();
    }
}

export abstract class GeneratedProof {
    readonly llmServiceInternal: LLMServiceInternal;
    readonly modelParams: ModelParams;
    readonly maxRoundsNumber: number;

    readonly proofGenerationContext: ProofGenerationContext;
    readonly proofVersions: ProofVersion[];

    constructor(
        proof: Proof,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ModelParams,
        llmServiceInternal: LLMServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        this.llmServiceInternal = llmServiceInternal;
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
        errorsHandlingMode: ErrorsHandlingMode,
        postprocessProof: (proof: string) => string = (proof) => proof
    ): Promise<GeneratedProof[]> {
        if (choices <= 0 || !this.nextVersionCanBeGenerated()) {
            return [];
        }
        const newProofs =
            await this.llmServiceInternal.llmService.generateFromChat(
                analyzedChat,
                this.modelParams,
                choices,
                errorsHandlingMode
            );
        return newProofs.map((proof: string) =>
            this.llmServiceInternal.constructGeneratedProof(
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
        choices: number = this.modelParams.multiroundProfile.proofFixChoices,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.LOG_EVENTS_AND_SWALLOW_ERRORS
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
            errorsHandlingMode,
            this.removeProofQedIfNeeded.bind(this)
        );
    }

    removeProofQedIfNeeded(message: string): string {
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
