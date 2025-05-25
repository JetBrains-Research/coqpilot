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
import { ProofGenerationMetadataHolder } from "../commonStructures/proofGenerationMetadata";
import { ProofGenerationType } from "../commonStructures/proofGenerationType";
import { ProofProviderRequest } from "../commonStructures/proofProviderRequest";
import { ProofVersion } from "../commonStructures/proofVersion";
import { SchedulersProviderBuilders } from "../commonStructures/schedulersProviders";
import { GeneratedProof } from "../generatedProof";
import { ModelParams } from "../modelParams";
import { ProofProvider } from "../proofProvider";
import { ProofProviderInternal } from "../proofProviderInternal";
import { throwConfigurationError } from "../utils/errorUtils";

import {
    ExternalProofProviderParams,
    resolveExternalProofProviderParamsWithDefaults,
} from "./abstractExternalProofProviderParams";
import { AbstractProofProviderInstaller } from "./installation/abstractProofProviderInstaller";

export abstract class AbstractExternalProofProvider<
    InputModelParams extends UserModelParams = UserModelParams,
    ResolvedModelParams extends ModelParams = ModelParams,
    InstallationOptions = any,
    ProofProviderType extends AbstractExternalProofProvider<
        UserModelParams,
        ResolvedModelParams,
        InstallationOptions,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
    ProofProviderInternalType extends AbstractExternalProofProviderInternal<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    > = any,
> extends ProofProvider<
    InputModelParams,
    ResolvedModelParams,
    ProofProviderType,
    GeneratedProofType,
    ProofProviderInternalType
> {
    abstract readonly installer: AbstractProofProviderInstaller<
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
        proofProviderParams: ExternalProofProviderParams = {}
    ) {
        const resolvedProofProviderParams =
            resolveExternalProofProviderParamsWithDefaults(
                proofProviderParams,
                externalProjectName,
                defaultMaxSubprocessesParallelism
            );
        super(resolvedProofProviderParams);

        this.installationPath = resolvedProofProviderParams.installationPath;
        this.maxSubprocessesSpawnedInParallel =
            resolvedProofProviderParams.maxSubprocessesSpawnedInParallel;
        this.clearProofGenerationLogsOnSuccess =
            resolvedProofProviderParams.clearProofGenerationLogsOnSuccess;

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

    isSameInstance(other: ProofProvider): boolean {
        return (
            other instanceof AbstractExternalProofProvider &&
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
        return `${AbstractExternalProofProvider.getDefaultInstallationDirPrefix(externalProjectName)}-v${PLUGIN_VERSION}`;
    }

    static getDefaultInstallationPath(externalProjectName: string): string {
        return joinPaths(
            getCoqPilotInstallationsDirPath(),
            AbstractExternalProofProvider.getDefaultInstallationRepoDirName(
                externalProjectName
            )
        );
    }
}

export abstract class AbstractExternalGeneratedProof<
    ResolvedModelParams extends ModelParams,
    ProofProviderType extends AbstractExternalProofProvider<
        UserModelParams,
        ResolvedModelParams,
        any,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    ProofProviderInternalType extends AbstractExternalProofProviderInternal<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
> extends GeneratedProof<
    ResolvedModelParams,
    ProofProviderType,
    GeneratedProofType,
    ProofProviderInternalType
> {
    constructor(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: ResolvedModelParams,
        proofProviderInternal: ProofProviderInternalType,
        previousProofVersions?: ProofVersion[]
    ) {
        super(
            rawProof,
            proofGenerationContext,
            modelParams,
            proofProviderInternal,
            previousProofVersions
        );
    }

    async fixProof(
        _diagnostic: string,
        choices: number = this.modelParams.multiroundProfile
            .defaultProofFixChoices
    ): Promise<GeneratedProofType[]> {
        this.proofProviderInternal.unsupportedMethod(
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

export abstract class AbstractExternalProofProviderInternal<
    ResolvedModelParams extends ModelParams,
    ProofProviderType extends AbstractExternalProofProvider<
        UserModelParams,
        ResolvedModelParams,
        any,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    GeneratedProofType extends AbstractExternalGeneratedProof<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
    ProofProviderInternalType extends AbstractExternalProofProviderInternal<
        ResolvedModelParams,
        ProofProviderType,
        GeneratedProofType,
        ProofProviderInternalType
    >,
> extends ProofProviderInternal<
    ResolvedModelParams,
    ProofProviderType,
    GeneratedProofType,
    ProofProviderInternalType
> {
    /**
     * Note: since `AbstractExternalProofProvider` already implements mechanism to limit parallelism
     * (by limiting max number of subprocesses spawned), no need in any additional one by default.
     */
    readonly modelsSchedulersProvider =
        SchedulersProviderBuilders.unlimitedParallelism(
            this.proofProvider.name,
            this.proofProviderSetup.enableModelsSchedulingDebugLogs
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
        _request: ProofProviderRequest,
        choices: number,
        proofGenerationContext: ProofGenerationContext
    ): void {
        ProofProviderInternal.validateChoices(choices);

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
            `\`${this.proofProvider.name}\` does not support generation from chat`,
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
