import { availableParallelism } from "os";

import { PLUGIN_VERSION } from "../../../extension/utils/pluginId";
import { EventLogger } from "../../../logging/eventLogger";
import { AsyncScheduler } from "../../../utils/async/asyncScheduler";
import { invariantFailed } from "../../../utils/errors/throwErrors";
// import { getCoqPilotInstallationsDirPath } from "../../../utils/fs/coqPilotInstallationsDir";
// import { joinPaths } from "../../../utils/fs/pathUtils";
import { Time, time } from "../../../utils/time";
import { ProofGenerationContext } from "../../proofGenerationContext";
import { MockRangoUserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory } from "../commonStructures/chat";
import { ErrorsHandlingMode } from "../commonStructures/errorsHandlingMode";
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
import { MockRangoModelParams } from "../modelParams";
import { throwConfigurationError } from "../utils/errorUtils";

import { runRangoProof } from "./rangoCore";
import { RangoModelParamsResolver } from "./rangoModelParamsResolver";

// TODO (refactor): make implementation of non-chat LLMService-s easier
// by providing default classes to extend

export class RangoService extends LLMServiceImpl<
    MockRangoUserModelParams,
    MockRangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    readonly serviceName = "RangoService";
    protected readonly internal = new RangoServiceInternal(
        this,
        this.eventLogger,
        this.generationsLoggerBuilder
    );
    protected readonly modelParamsResolver = new RangoModelParamsResolver();

    static readonly DEFAULT_RANGO_DIR_PREFIX = "coqpilot-rango";
    static readonly DEFAULT_RANGO_REPO_DIR_NAME = `${this.DEFAULT_RANGO_DIR_PREFIX}-v${PLUGIN_VERSION}`;

    private static readonly MAX_HEURISTIC_SUBPROCESSES_PARALLELISM = 1;

    constructor(
        eventLogger: EventLogger | undefined = undefined,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.RETHROW_ERRORS,
        generationLogsFilePath: string | undefined = undefined,
        debugLogs: boolean = false,
        readonly rangoDirPath: string = "/content/rango",
        readonly maxSubprocessesSpawnedInParallel: number = Math.min(
            availableParallelism(),
            RangoService.MAX_HEURISTIC_SUBPROCESSES_PARALLELISM
        ),
        readonly clearProofGenerationLogsOnSuccess: boolean = true
    ) {
        super(
            eventLogger,
            errorsHandlingMode,
            generationLogsFilePath,
            debugLogs
        );
    }

    private readonly subprocessesScheduler = new AsyncScheduler(
        this.maxSubprocessesSpawnedInParallel,
        true,
        `Rango Subprocesses Scheduler <max ${this.maxSubprocessesSpawnedInParallel} sub-s>`
    );

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: MockRangoModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        abortSignal?: AbortSignal
    ): Promise<RangoGeneratedProof[]> {
        return this.internal.logGenerationAndHandleErrors(
            ProofGenerationType.NO_CHAT,
            params,
            choices,
            metadataHolder,
            (_request) => {
                LLMServiceInternal.validateChoices(choices);
                if (choices !== 1) {
                    throwConfigurationError(
                        `requested ${choices} choices, but only \`1\` is supported: `,
                        "Rango performs whole proof search by itself, ",
                        "resulting in either single valid proof or none of them"
                    );
                }
                if (
                    proofGenerationContext.externalPipelineContext === undefined
                ) {
                    throwConfigurationError(
                        `external pipeline context has not been built: `,
                        "most likely, the provided data is insufficient ",
                        "(e.g., the project root may not be set)"
                    );
                }
            },
            async (_request) =>
                this.subprocessesScheduler.scheduleTask(
                    async () => {
                        const externalPipelineContext =
                            proofGenerationContext.externalPipelineContext ??
                            invariantFailed(
                                "Rango",
                                "`proofGenerationContext` has no built `externalPipelineContext`, ",
                                "required to execute Rango proof generation"
                            );
                        // TODO: search for `openai.AuthenticationError` error in logs and report as configuration error
                        const proofOrUndefined = await runRangoProof(
                            externalPipelineContext,
                            params,
                            this.rangoDirPath,
                            this.clearProofGenerationLogsOnSuccess,
                            this.internal.logDebug,
                            abortSignal
                        );
                        const rawProofsContent: string[] =
                            proofOrUndefined === undefined
                                ? []
                                : [proofOrUndefined];
                        return {
                            items: rawProofsContent.map((content) => {
                                return {
                                    content: content,
                                    tokensSpent: zeroTokens(),
                                };
                            }),
                            tokensSpentInTotal: zeroTokens(), // TODO: extract tokens info from Rango
                        };
                    },
                    (schedulerMessage: string) =>
                        this.internal.logDebug.event(schedulerMessage)
                ),
            (rawProof) =>
                this.internal.constructGeneratedProof(
                    rawProof,
                    proofGenerationContext,
                    params
                )
        );
    }

    estimateTimeToBecomeAvailable(): Time {
        return time(5, "second"); // some cool-down for the subprocess spawning
    }
}

export class RangoGeneratedProof extends GeneratedProofImpl<
    MockRangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockRangoModelParams,
        llmServiceInternal: RangoServiceInternal,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            llmServiceInternal,
            previousProofVersions
        );
    }

    async fixProof(
        _diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices
    ): Promise<RangoGeneratedProof[]> {
        this.llmServiceInternal.unsupportedMethod(
            "`RangoGeneratedProof` cannot be fixed",
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

class RangoServiceInternal extends LLMServiceInternal<
    MockRangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: MockRangoModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): RangoGeneratedProof {
        return new RangoGeneratedProof(
            rawProof,
            proofGenerationContext,
            modelParams,
            this,
            previousProofVersions
        );
    }

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: MockRangoModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        this.unsupportedMethod(
            "`RangoService` does not support generation from chat",
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
