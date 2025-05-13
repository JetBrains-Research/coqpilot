import { PLUGIN_VERSION } from "../../../extension/utils/pluginId";
import { AsyncScheduler } from "../../../utils/async/asyncScheduler";
import { invariantFailed } from "../../../utils/errors/throwErrors";
import { getCoqPilotInstallationsDirPath } from "../../../utils/fs/coqPilotInstallationsDir";
import { translateToSafeFileName } from "../../../utils/fs/fileNameUtils";
import { joinPaths } from "../../../utils/fs/pathUtils";
import { MessageHandler } from "../../../utils/structures/messageHandler";
import { Time, time } from "../../../utils/time";
import {
    ExternalPipelineProofGenerationContext,
    ProofGenerationContext,
} from "../../proofGenerationContext";
import { UserModelParams } from "../../userModelParams";
import { AnalyzedChatHistory } from "../commonStructures/chat";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { zeroTokens } from "../commonStructures/generationTokens";
import { InstallerProvider } from "../commonStructures/installerProvider";
import { LLMServiceRequest } from "../commonStructures/llmServiceRequest";
import { ProofGenerationMetadataHolder } from "../commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "../commonStructures/proofGenerationType";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProofImpl } from "../generatedProof";
import { LLMService, LLMServiceImpl } from "../llmService";
import { LLMServiceInternal } from "../llmServiceInternal";
import { ModelParams } from "../modelParams";
import { throwConfigurationError } from "../utils/errorUtils";

import {
    ExternalServiceParams,
    resolveExternalServiceParamsWithDefaults,
} from "./abstractExternalServiceParams";
import { AbstractExternalServiceInstaller } from "./installation/abstractExternalServiceInstaller";

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
    readonly installerProvider: InstallerProvider = () => {
        return {
            installer: this.installer,
            options: undefined,
        };
    };
    readonly installationPath: string;
    readonly clearProofGenerationLogsOnSuccess: boolean;

    protected readonly maxSubprocessesSpawnedInParallel: number;
    protected readonly subprocessesScheduler: AsyncScheduler;

    constructor(
        readonly externalProjectName: string,
        readonly defaultMaxSubprocessesParallelism: number,
        serviceParams: ExternalServiceParams = {}
    ) {
        const resolvedServiceParams = resolveExternalServiceParamsWithDefaults(
            serviceParams,
            externalProjectName,
            defaultMaxSubprocessesParallelism
        );
        super(resolvedServiceParams);

        this.installationPath = resolvedServiceParams.installationPath;
        this.maxSubprocessesSpawnedInParallel =
            resolvedServiceParams.maxSubprocessesSpawnedInParallel;
        this.clearProofGenerationLogsOnSuccess =
            resolvedServiceParams.clearProofGenerationLogsOnSuccess;

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
        abortSignal?: AbortSignal,
        onSchedulerDebugLog: MessageHandler = this.internal
            .sendDebugEventOnSchedulerLog
    ): Promise<GeneratedProofType[]> {
        return this.internal.scheduleLoggedGenerationAndHandleErrors(
            ProofGenerationType.NO_CHAT,
            params,
            choices,
            metadataHolder,
            onSchedulerDebugLog,
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

    isSameInstance(other: LLMService): boolean {
        return (
            other instanceof AbstractExternalService &&
            this.installationPath === other.installationPath
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
    /**
     * Note: since `AbstractExternalService` already implements mechanism to limit parallelism
     * (by limiting max number of subprocesses spawned), no need in any additional one by default.
     */
    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.llmService.name,
            this.serviceSetup.enableModelsSchedulingDebugLogs
        );

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
            `\`${this.llmService.name}\` does not support generation from chat`,
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
