import { availableParallelism } from "os";

import { PLUGIN_VERSION } from "../../../extension/utils/pluginId";
import { EventLogger } from "../../../logging/eventLogger";
import { AsyncScheduler } from "../../../utils/async/asyncScheduler";
import { invariantFailed } from "../../../utils/errors/throwErrors";
import { getCoqPilotInstallationsDirPath } from "../../../utils/fs/coqPilotInstallationsDir";
import { translateToSafeFileName } from "../../../utils/fs/fileNameUtils";
import { joinPaths } from "../../../utils/fs/pathUtils";
import { Time, time } from "../../../utils/time";
import {
    ExternalPipelineProofGenerationContext,
    ProofGenerationContext,
} from "../../proofGenerationContext";
import { UserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory } from "../commonStructures/chat";
import { ErrorsHandlingMode } from "../commonStructures/errorsHandlingMode";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { zeroTokens } from "../commonStructures/generationTokens";
import { LLMServiceRequest } from "../commonStructures/llmServiceRequest";
import { ProofGenerationMetadataHolder } from "../commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "../commonStructures/proofGenerationType";
import { ProofVersion } from "../commonStructures/proofVersion";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { ModelParams } from "../modelParams";
import { throwConfigurationError } from "../utils/errorUtils";

import { AbstractExternalServiceInstaller } from "./installation/abstractLLMServiceInstaller";

export type ExternalService<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    InstallationOptions,
> = AbstractExternalService<
    InputModelParams,
    ResolvedModelParams,
    InstallationOptions,
    any,
    any,
    any
>;

export abstract class AbstractExternalService<
    InputModelParams extends UserModelParams,
    ResolvedModelParams extends ModelParams,
    InstallationOptions,
    LLMServiceType extends AbstractExternalService<
        UserModelParams,
        ResolvedModelParams,
        InstallationOptions,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    LLMServiceInternalType extends AbstractExternalServiceInternal<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
> extends LLMServiceImpl<
    InputModelParams,
    ResolvedModelParams,
    LLMServiceType,
    GeneratedProofType,
    LLMServiceInternalType
> {
    abstract readonly installer: AbstractExternalServiceInstaller<
        InstallationOptions,
        InputModelParams
    >;

    protected readonly maxSubprocessesSpawnedInParallel: number;
    protected readonly subprocessesScheduler: AsyncScheduler;

    // TODO: put most of the options to a separate object and pass it, resolving the defaults
    constructor(
        readonly externalProjectName: string,
        readonly defaultMaxSubprocessesParallelism: number,
        eventLogger: EventLogger | undefined = undefined,
        errorsHandlingMode: ErrorsHandlingMode = ErrorsHandlingMode.RETHROW_ERRORS,
        generationLogsFilePath: string | undefined = undefined,
        debugLogs: boolean = false,
        readonly installationPath: string = AbstractExternalService.getDefaultInstallationPath(
            externalProjectName
        ),
        maxSubprocessesSpawnedInParallel: number | undefined = undefined,
        readonly clearProofGenerationLogsOnSuccess: boolean = true
    ) {
        super(
            eventLogger,
            errorsHandlingMode,
            generationLogsFilePath,
            debugLogs
        );
        this.maxSubprocessesSpawnedInParallel =
            maxSubprocessesSpawnedInParallel ??
            this.getDefaultMaxSubprocessesSpawnedInParallel();
        this.subprocessesScheduler = new AsyncScheduler(
            this.maxSubprocessesSpawnedInParallel,
            true,
            `${this.externalProjectName} Subprocesses Scheduler <max ${this.maxSubprocessesSpawnedInParallel} sub-s>`
        );
    }

    async generateProof(
        proofGenerationContext: ProofGenerationContext,
        params: ResolvedModelParams,
        choices: number = params.defaultChoices,
        metadataHolder: ProofGenerationMetadataHolder | undefined = undefined,
        abortSignal?: AbortSignal
    ): Promise<GeneratedProofType[]> {
        return this.internal.logGenerationAndHandleErrors(
            ProofGenerationType.NO_CHAT,
            params,
            choices,
            metadataHolder,
            (request) =>
                this.internal.validateGenerationRequestOrThrow(
                    request,
                    choices,
                    proofGenerationContext
                ),
            async (_request) =>
                this.subprocessesScheduler.scheduleTask(
                    async () => {
                        const externalPipelineContext =
                            proofGenerationContext.externalPipelineContext ??
                            invariantFailed(
                                this.externalProjectName,
                                "`proofGenerationContext` has no built `externalPipelineContext`, ",
                                `required to execute ${this.externalProjectName} proof generation`
                            );
                        return await this.internal.performExternalProofGeneration(
                            externalPipelineContext,
                            params,
                            choices,
                            abortSignal
                        );
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

    protected getDefaultMaxSubprocessesSpawnedInParallel(): number {
        return Math.min(
            availableParallelism(),
            this.defaultMaxSubprocessesParallelism
        );
    }

    static getDefaultInstallationDirPrefix(
        externalProjectName: string
    ): string {
        return `coqpilot-${translateToSafeFileName(externalProjectName)}`;
    }

    static getDefaultInstallationRepoDirName(
        externalProjectName: string
    ): string {
        return `${AbstractExternalService.getDefaultInstallationDirPrefix(externalProjectName)}-v${PLUGIN_VERSION}`;
    }

    static getDefaultInstallationPath(externalProjectName: string): string {
        return joinPaths(
            getCoqPilotInstallationsDirPath(),
            AbstractExternalService.getDefaultInstallationRepoDirName(
                externalProjectName
            )
        );
    }
}

export abstract class AbstractExternalGeneratedProof<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends AbstractExternalService<
        UserModelParams,
        ResolvedModelParams,
        any,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    LLMServiceInternalType extends AbstractExternalServiceInternal<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
> extends GeneratedProofImpl<
    ResolvedModelParams,
    LLMServiceType,
    GeneratedProofType,
    LLMServiceInternalType
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ResolvedModelParams,
        llmServiceInternal: LLMServiceInternalType,
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
    ): Promise<GeneratedProofType[]> {
        this.llmServiceInternal.unsupportedMethod(
            "`ExternalGeneratedProof` cannot be fixed",
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

export abstract class AbstractExternalServiceInternal<
    ResolvedModelParams extends ModelParams,
    LLMServiceType extends AbstractExternalService<
        UserModelParams,
        ResolvedModelParams,
        any,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
    LLMServiceInternalType extends AbstractExternalServiceInternal<
        ResolvedModelParams,
        LLMServiceType,
        GeneratedProofType,
        LLMServiceInternalType
    >,
> extends LLMServiceInternal<
    ResolvedModelParams,
    LLMServiceType,
    GeneratedProofType,
    LLMServiceInternalType
> {
    abstract constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ResolvedModelParams,
        previousProofVersions?: ProofVersion[] | undefined
    ): GeneratedProofType;

    abstract performExternalProofGeneration(
        externalPipelineContext: ExternalPipelineProofGenerationContext,
        params: ResolvedModelParams,
        choices: number,
        abortSignal?: AbortSignal
    ): Promise<GeneratedRawContent>;

    /**
     * Provide additional generation request validation.
     * Basic non-zero `choices` and defined `externalPipelineContext` validations
     * are implemented by default.
     */
    validateGenerationRequestOrThrow(
        _request: LLMServiceRequest,
        choices: number,
        proofGenerationContext: ProofGenerationContext
    ): void {
        LLMServiceInternal.validateChoices(choices);

        if (proofGenerationContext.externalPipelineContext === undefined) {
            throwConfigurationError(
                `external pipeline context has not been built: `,
                "most likely, the provided data is insufficient ",
                "(e.g., the project root may not be set)"
            );
        }
    }

    async generateFromChatImpl(
        _analyzedChat: AnalyzedChatHistory,
        _params: ResolvedModelParams,
        _choices: number
    ): Promise<GeneratedRawContent> {
        this.unsupportedMethod(
            `\`${this.llmService.serviceName}\` does not support generation from chat`,
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
