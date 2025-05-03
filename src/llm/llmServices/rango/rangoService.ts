import {
    ExternalPipelineProofGenerationContext,
    ProofGenerationContext,
} from "../../proofGenerationContext";
import { RangoUserModelParams } from "../../userModelParams";
import {
    AbstractExternalGeneratedProof,
    AbstractExternalService,
    AbstractExternalServiceInternal,
} from "../abstractExternalService/abstractExternalService";
import { ExternalServiceParams } from "../abstractExternalService/abstractExternalServiceParams";
import {
    GeneratedRawContent,
    GeneratedRawContentItem,
} from "../commonStructures/generatedRawContent";
import { zeroTokens } from "../commonStructures/generationTokens";
import { LLMServiceRequest } from "../commonStructures/llmServiceRequest";
import { ProofVersion } from "../commonStructures/proofVersion";
import { RangoModelParams } from "../modelParams";
import { throwConfigurationError } from "../utils/errorUtils";

import { runRangoProof } from "./rangoCore";
import { RangoInstallationOptions, RangoInstaller } from "./rangoInstaller";
import { RangoModelParamsResolver } from "./rangoModelParamsResolver";

export class RangoService extends AbstractExternalService<
    RangoUserModelParams,
    RangoModelParams,
    RangoInstallationOptions,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {
    readonly serviceName = "RangoService";
    static readonly externalProjectName = "Rango";

    constructor(serviceParams: ExternalServiceParams = {}) {
        super(RangoService.externalProjectName, 3, serviceParams);
    }

    protected readonly internal = new RangoServiceInternal(
        this,
        this.eventLogger,
        this.generationsLoggerBuilder
    );
    protected readonly modelParamsResolver = new RangoModelParamsResolver();

    readonly installer = new RangoInstaller();
}

export class RangoGeneratedProof extends AbstractExternalGeneratedProof<
    RangoModelParams,
    RangoService,
    RangoGeneratedProof,
    RangoServiceInternal
> {}

class RangoServiceInternal extends AbstractExternalServiceInternal<
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
        request: LLMServiceRequest,
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
            this.llmService.installationPath,
            this.llmService.clearProofGenerationLogsOnSuccess,
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
