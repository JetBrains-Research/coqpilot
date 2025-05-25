import {
    ExternalPipelineProofGenerationContext,
    ProofGenerationContext,
} from "../../proofGenerationContext";
import { RangoUserModelParams } from "../../userModelParams";
import {
    AbstractExternalGeneratedProof,
    AbstractExternalProofProvider,
    AbstractExternalProofProviderInternal,
} from "../abstractExternalProofProvider/abstractExternalProofProvider";
import { ExternalProofProviderParams } from "../abstractExternalProofProvider/abstractExternalProofProviderParams";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { zeroTokens } from "../commonStructures/generationTokens";
import { ProofProviderRequest } from "../commonStructures/proofProviderRequest";
import { ProofVersion } from "../commonStructures/proofVersion";
import { RangoModelParams } from "../modelParams";
import { ProofProviderIdentifier } from "../proofProviderIdentifier";
import { throwConfigurationError } from "../utils/errorUtils";
import { provideBasicSerializer } from "../utils/serialization/basicProofProviderSerializer";

import { runRangoProof } from "./rangoCore";
import { RangoInstallationOptions, RangoInstaller } from "./rangoInstaller";
import { RangoModelParamsResolver } from "./rangoModelParamsResolver";

export class RangoService extends AbstractExternalProofProvider<
    RangoUserModelParams,
    RangoModelParams,
    RangoInstallationOptions,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    readonly name = "RangoService";
    readonly identifier = ProofProviderIdentifier.RANGO;

    static readonly externalProjectName = "Rango";
    static readonly DEFAULT_MAX_SUBPROCESSES_PARALLELISM = 3;

    constructor(proofProviderParams: ExternalProofProviderParams = {}) {
        super(
            RangoService.externalProjectName,
            RangoService.DEFAULT_MAX_SUBPROCESSES_PARALLELISM,
            proofProviderParams
        );
    }

    protected readonly internal = new RangoServiceInternal(this);
    protected readonly modelParamsResolver = new RangoModelParamsResolver();
    protected readonly serializer = provideBasicSerializer(this);

    readonly installer = new RangoInstaller();
}

export class RangoGeneratedProof extends AbstractExternalGeneratedProof<
    RangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {}

class RangoServiceInternal extends AbstractExternalProofProviderInternal<
    RangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    constructGeneratedProof(
        rawProof: GeneratedRawContentItem,
        proofGenerationContext: ProofGenerationContext,
        modelParams: RangoModelParams,
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

    validateGenerationRequestOrThrow(
        request: ProofProviderRequest,
        choices: number,
        proofGenerationContext: ProofGenerationContext
    ): void {
        super.validateGenerationRequestOrThrow(
            request,
            choices,
            proofGenerationContext
        );
        if (choices !== 1) {
            throwConfigurationError(
                `requested ${choices} choices, but only \`1\` is supported: `,
                "Rango performs whole proof search by itself, ",
                "resulting in either single valid proof or none of them"
            );
        }
    }

    async performExternalProofGeneration(
        externalPipelineContext: ExternalPipelineProofGenerationContext,
        params: RangoModelParams,
        _choices: number,
        abortSignal?: AbortSignal
    ): Promise<GeneratedRawContent> {
        // TODO: search for `openai.AuthenticationError` error in logs and report as configuration error
        const proofOrUndefined = await runRangoProof(
            externalPipelineContext,
            params,
            this.proofProvider.installationPath,
            this.proofProvider.clearProofGenerationLogsOnSuccess,
            this.logDebug,
            abortSignal
        );
        const rawProofsContent: string[] =
            proofOrUndefined === undefined ? [] : [proofOrUndefined];
        return {
            items: rawProofsContent.map((content) => {
                return {
                    content: content,
                    tokensSpent: zeroTokens(),
                };
            }),
            tokensSpentInTotal: zeroTokens(), // TODO: extract tokens info from Rango
        };
    }
}
