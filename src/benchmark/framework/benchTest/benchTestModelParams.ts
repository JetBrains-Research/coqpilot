import { JSONSchemaType } from "ajv";
import { PropertiesSchema } from "ajv/dist/types/json-schema";

import {
    ModelParams,
    modelParamsSchema,
} from "../../../llm/llmServices/modelParams";
import { ValidationRules } from "../../../llm/llmServices/utils/paramsResolvers/builders";
import { BasicModelParamsResolver } from "../../../llm/llmServices/utils/paramsResolvers/kit/basicModelParamsResolvers";
import { ValidParamsResolverImpl } from "../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../llm/userModelParams";

import { InputBenchmarkingModelParams } from "../structures/inputParameters/inputBenchmarkingModelParams";

export interface BenchTestUserModelParams extends UserModelParams {
    testModelName?: string;
    tactics: string[];
    generationMillis: number;
}

export interface BenchTestModelParams extends ModelParams {
    testModelName: string;
    tactics: string[];
    generationMillis: number;
}

export interface BenchTestInputBenchmarkingModelParams
    extends BenchTestUserModelParams,
        InputBenchmarkingModelParams.Params {}

export namespace BenchTestModelParamsDefaults {
    export const DEFAULT_TEST_MODEL_NAME = "bench-test-model";
    export const DEFAULT_GENERATION_MILLIS = 0;
}

export const benchTestModelParamsSchema: JSONSchemaType<BenchTestModelParams> =
    {
        title: "benchTestModelsParameters",
        type: "object",
        properties: {
            testModelName: {
                type: "string",
            },
            tactics: {
                type: "array",
                items: { type: "string" },
            },
            generationMillis: {
                type: "number",
            },
            ...(modelParamsSchema.properties as PropertiesSchema<ModelParams>),
        },
        required: [
            "testModelName",
            "tactics",
            "generationMillis",
            ...modelParamsSchema.required,
        ],
        additionalProperties: false,
    };

export class BenchTestModelParamsResolver
    extends BasicModelParamsResolver<
        BenchTestUserModelParams,
        BenchTestModelParams
    >
    implements
        ValidParamsResolverImpl<BenchTestUserModelParams, BenchTestModelParams>
{
    constructor() {
        super(benchTestModelParamsSchema, "BenchTestModelParams");
    }

    readonly testModelName = this.resolveParam<string>("testModelName")
        .default(() => BenchTestModelParamsDefaults.DEFAULT_TEST_MODEL_NAME)
        .validateAtRuntimeOnly();

    readonly tactics = this.resolveParam<string[]>("tactics")
        .requiredToBeConfigured()
        .validate([(value) => value.length > 0, "be non-empty"]);

    readonly generationMillis = this.resolveParam<number>("generationMillis")
        .default(() => BenchTestModelParamsDefaults.DEFAULT_GENERATION_MILLIS)
        .validate(ValidationRules.beNonNegativeNumber);

    readonly defaultChoices = this.resolveParam<number>("choices")
        .default((inputParams) => inputParams.tactics.length)
        .validate(
            [(value) => value >= 0, "be non-negative"],
            [
                (value, inputParams) => value <= inputParams.tactics.length,
                (inputParams) =>
                    `be less than or equal to the total number of \`tactics\` (${inputParams.tactics.length} for the specified \`tactics\`)`,
            ]
        );

    // So far tokens properties are not used, so they are configured with mocks

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock((inputParams) =>
        Math.max(0, ...inputParams.tactics.map((tactic) => tactic.length))
    );

    readonly tokensLimit = this.resolveParam<number>(
        "tokensLimit"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);
}
