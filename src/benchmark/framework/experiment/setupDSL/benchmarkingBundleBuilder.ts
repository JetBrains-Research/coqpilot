import { selectProofProviderConstructor } from "../../../../proofProviders/impl/proofProviderConstructor";
import { ProofProviderConstructor } from "../../../../proofProviders/impl/proofProviderConstructor";
import {
    CorrespondingIdentifier,
    CorrespondingInputProofProviderParams,
    ProofProviderStringIdentifier,
    toEnumIdentifier,
} from "../../../../proofProviders/impl/proofProviderIdentifier";
import { ConfigurationError } from "../../../../proofProviders/proofProviderErrors";

import { findFirstDuplicate } from "../../../../utils/collectionUtils/listUtils";
import {
    DatasetInputTargets,
    mergeInputTargets,
} from "../../structures/common/inputTargets";
import {
    CorrespondingInputParams,
    InputBenchmarkingModelParams,
} from "../../structures/inputParameters/inputBenchmarkingModelParams";
import { AbstractExperiment } from "../abstractExperiment";

export class BenchmarkingBundle {
    constructor() {}

    withProofProvider<T extends ProofProviderStringIdentifier>(
        proofProviderStringIdentifier: T,
        proofProviderParams?: CorrespondingInputProofProviderParams<
            CorrespondingIdentifier<T>
        >
    ): BenchmarkingBundleWithProofProvider<
        CorrespondingInputParams<CorrespondingIdentifier<T>>
    > {
        const identifier = toEnumIdentifier(proofProviderStringIdentifier);
        return new BenchmarkingBundleWithProofProvider(
            selectProofProviderConstructor(
                identifier,
                proofProviderParams ?? {}
            )
        );
    }

    withCustomProofProvider<
        InputParams extends InputBenchmarkingModelParams.Params,
    >(
        proofProviderConstructor: ProofProviderConstructor
    ): BenchmarkingBundleWithProofProvider<InputParams> {
        return new BenchmarkingBundleWithProofProvider(
            proofProviderConstructor
        );
    }
}

export class BenchmarkingBundleWithProofProvider<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    constructor(
        private readonly proofProviderConstructor: ProofProviderConstructor
    ) {}

    withBenchmarkingModelsParamsCommons<
        InputParamsCommons extends Partial<InputParams>,
    >(commons: InputParamsCommons) {
        return new BenchmarkingBundleWithModelsParamsCommons<
            InputParams,
            InputParamsCommons
        >(this, commons);
    }

    withBenchmarkingModelsParams(
        ...inputParams: InputParams[]
    ): BenchmarkingBundleWithModelsParams<InputParams> {
        this.throwOnDuplicateModelIds(inputParams);
        return new BenchmarkingBundleWithModelsParams(
            this.proofProviderConstructor,
            inputParams
        );
    }

    /**
     * Note: unfortunately, this check is not sufficient to prevent
     * models from different bundles having clashing `modelId`-s;
     * however, this check protects from a basic mistake.
     */
    private throwOnDuplicateModelIds(inputParams: InputParams[]) {
        const modelIds = inputParams.map((params) => params.modelId);
        const duplicateModelId = findFirstDuplicate(modelIds);
        if (duplicateModelId !== undefined) {
            throw new ConfigurationError(
                `models' identifiers are not unique: several models have \`modelId: "${duplicateModelId}"\``
            );
        }
    }
}

export class BenchmarkingBundleWithModelsParamsCommons<
    InputParams extends InputBenchmarkingModelParams.Params,
    InputParamsCommons extends Partial<InputParams>,
> {
    constructor(
        private readonly parentBundle: BenchmarkingBundleWithProofProvider<InputParams>,
        private readonly modelsParamsCommons: InputParamsCommons
    ) {}

    withBenchmarkingModelsParams(
        ...inputBenchmarkingModelsParams: (Omit<
            InputParams,
            keyof Required<InputParamsCommons>
        > &
            Partial<Required<InputParamsCommons>>)[] // comment `& ...` to forbid overriding common properties
    ): BenchmarkingBundleWithModelsParams<InputParams> {
        return this.parentBundle.withBenchmarkingModelsParams(
            ...inputBenchmarkingModelsParams.map((params) => {
                // Indeed, here undefined value can be passed for a required property (through `inputParam`).
                // However, it will be checked later at the resolution stage and the error will be thrown.
                return {
                    ...this.modelsParamsCommons,
                    ...params,
                } as unknown as InputParams;
            })
        );
    }
}

export class BenchmarkingBundleWithModelsParams<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    constructor(
        private readonly proofProviderConstructor: ProofProviderConstructor,
        private readonly inputBenchmarkingModelsParams: InputParams[]
    ) {}

    withTargets(
        ...targets: DatasetInputTargets[]
    ): BenchmarkingBundleWithTargets<InputParams> {
        return new BenchmarkingBundleWithTargets(
            this.proofProviderConstructor,
            this.inputBenchmarkingModelsParams,
            targets
        );
    }
}

export class BenchmarkingBundleWithTargets<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    constructor(
        private readonly proofProviderConstructor: ProofProviderConstructor,
        private readonly inputBenchmarkingModelsParams: InputParams[],
        private readonly targets: DatasetInputTargets[]
    ) {}

    addTo(experiment: AbstractExperiment) {
        experiment.addBundle({
            proofProviderConstructor: this.proofProviderConstructor,
            inputBenchmarkingModelsParams: this.inputBenchmarkingModelsParams,
            requestedTargets: mergeInputTargets(this.targets).resolveRequests(),
        });
    }
}
