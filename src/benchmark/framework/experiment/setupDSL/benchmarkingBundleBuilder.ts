import { ConfigurationError } from "../../../../llm/llmServiceErrors";

import { findFirstDuplicate } from "../../../../utils/collectionUtils/listUtils";
import {
    DatasetInputTargets,
    mergeInputTargets,
} from "../../structures/common/inputTargets";
import {
    CorrespondingInputParams,
    CorrespondingInputServiceParams,
    LLMServiceStringIdentifier,
} from "../../structures/common/llmServiceIdentifier";
import { InputBenchmarkingModelParams } from "../../structures/inputParameters/inputBenchmarkingModelParams";
import { BasicLLMServiceProvider } from "../../structures/llmServiceProvider/basicLLMServiceProvider";
import { LLMServiceProvider } from "../../structures/llmServiceProvider/llmServiceProvider";
import { AbstractExperiment } from "../abstractExperiment";

export class BenchmarkingBundle {
    constructor() {}

    withLLMService<T extends LLMServiceStringIdentifier>(
        llmServiceStringIdentifier: T,
        serviceParams?: CorrespondingInputServiceParams<T>
    ): BenchmarkingBundleWithLLMService<CorrespondingInputParams<T>> {
        return new BenchmarkingBundleWithLLMService(
            new BasicLLMServiceProvider(
                llmServiceStringIdentifier,
                serviceParams
            )
        );
    }
}

export class BenchmarkingBundleWithLLMService<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    constructor(private readonly llmServiceProvider: LLMServiceProvider) {}

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
            this.llmServiceProvider,
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
        private readonly parentBundle: BenchmarkingBundleWithLLMService<InputParams>,
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
        private readonly llmServiceProvider: LLMServiceProvider,
        private readonly inputBenchmarkingModelsParams: InputParams[]
    ) {}

    withTargets(
        ...targets: DatasetInputTargets[]
    ): BenchmarkingBundleWithTargets<InputParams> {
        return new BenchmarkingBundleWithTargets(
            this.llmServiceProvider,
            this.inputBenchmarkingModelsParams,
            targets
        );
    }
}

export class BenchmarkingBundleWithTargets<
    InputParams extends InputBenchmarkingModelParams.Params,
> {
    constructor(
        private readonly llmServiceProvider: LLMServiceProvider,
        private readonly inputBenchmarkingModelsParams: InputParams[],
        private readonly targets: DatasetInputTargets[]
    ) {}

    addTo(experiment: AbstractExperiment) {
        experiment.addBundle({
            llmServiceProvider: this.llmServiceProvider,
            inputBenchmarkingModelsParams: this.inputBenchmarkingModelsParams,
            requestedTargets: mergeInputTargets(this.targets).resolveRequests(),
        });
    }
}
