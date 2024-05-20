import { JSONSchemaType } from "ajv";
import { expect } from "earl";

import { ModelParams } from "../../../../llm/llmServices/modelParams";
import { ParamsResolver } from "../../../../llm/llmServices/utils/paramsResolvers/abstractResolvers";
import { ValidationRules } from "../../../../llm/llmServices/utils/paramsResolvers/builders";
import {
    NoOptionalProperties,
    ParamsResolverImpl,
} from "../../../../llm/llmServices/utils/paramsResolvers/paramsResolverImpl";
import { UserModelParams } from "../../../../llm/userModelParams";

// import { UserModelParams } from "../../../../llm/userModelParams";
import { expectParamResolutionResult } from "../../llmSpecificTestUtils/expectResolutionResult";

suite("[LLMService-s utils] Test `ParamsResolver`", () => {
    const positiveInputValue = 5;
    const negativeInputValue = -5;
    const positiveDefaultValue = 6;

    function testSuccessfulSingleNumberResolution<InputType, ResolveToType>(
        testName: string,
        paramsResolver: ParamsResolver<InputType, ResolveToType>,
        inputParams: InputType,
        expectedResolvedParams: ResolveToType,
        expectedParamNameInLogs: string
    ) {
        test(testName, () => {
            const resolutionResult = paramsResolver.resolve(inputParams);
            expect(resolutionResult.resolved).toEqual(expectedResolvedParams);
            expect(resolutionResult.resolutionLogs).toHaveLength(1);
            expectParamResolutionResult(
                resolutionResult.resolutionLogs[0],
                {
                    resultValue: positiveInputValue,
                    inputReadCorrectly: {
                        wasPerformed: true,
                        withValue: positiveInputValue,
                    },
                },
                expectedParamNameInLogs
            );
        });
    }

    function testFailedSingleNumberResolution<InputType, ResolveToType>(
        testName: string,
        paramsResolver: ParamsResolver<InputType, ResolveToType>,
        inputParams: InputType,
        expectedParamNameInLogs: string
    ) {
        test(testName, () => {
            const resolutionResult = paramsResolver.resolve(inputParams);
            expect(resolutionResult.resolved).toBeNullish();
            expect(resolutionResult.resolutionLogs).toHaveLength(1);
            expectParamResolutionResult(
                resolutionResult.resolutionLogs[0],
                {
                    isInvalidCause: "should be positive, but has value",
                    inputReadCorrectly: {
                        wasPerformed: true,
                        withValue: negativeInputValue,
                    },
                },
                expectedParamNameInLogs
            );
        });
    }

    interface InputNumberParam {
        input?: number;
    }

    interface ResolvedNumberParam {
        output: number;
    }

    const resolvedNumberParamSchema: JSONSchemaType<ResolvedNumberParam> = {
        type: "object",
        properties: {
            output: { type: "number" },
        },
        required: ["output"],
        additionalProperties: false,
    };

    class NumberParamResolver extends ParamsResolverImpl<
        InputNumberParam,
        ResolvedNumberParam
    > {
        constructor() {
            super(resolvedNumberParamSchema, "ResolvedNumberParam");
        }

        readonly output = this.resolveParam<number>("input")
            .default(() => positiveDefaultValue)
            .validate(ValidationRules.bePositiveNumber);
    }

    (
        [
            ["1-to-1 params", { input: positiveInputValue }],
            [
                "with-extra-to-1 params",
                { input: positiveInputValue, extra: true } as InputNumberParam,
            ],
        ] as [string, InputNumberParam][]
    ).forEach(([testCase, inputParams]) => {
        testSuccessfulSingleNumberResolution(
            `\`ParamsResolver\` with single value: ${testCase}, success`,
            new NumberParamResolver(),
            inputParams,
            {
                output: positiveInputValue,
            },
            "input"
        );
    });

    testFailedSingleNumberResolution(
        "`ParamsResolver` with single value: 1-to-1 params, failure",
        new NumberParamResolver(),
        {
            input: negativeInputValue,
        },
        "input"
    );

    interface InputMixedParams {
        input?: number;
        complex?: ResolvedNumberParam;
        extra: string;
    }

    interface ResolvedMixedParams {
        output: number;
        complex: ResolvedNumberParam;
        inserted: boolean;
    }

    class MixedParamsResolver extends ParamsResolverImpl<
        InputMixedParams,
        ResolvedMixedParams
    > {
        constructor() {
            super(
                {
                    type: "object",
                    properties: {
                        output: { type: "number" },
                        complex: {
                            type: "object",
                            oneOf: [resolvedNumberParamSchema],
                        },
                        inserted: { type: "boolean" },
                    },
                    required: ["output", "complex", "inserted"],
                },
                "ResolvedMixedParams"
            );
        }

        readonly output = this.resolveParam<number>("input")
            .requiredToBeConfigured()
            .validate(ValidationRules.bePositiveNumber);

        readonly complex = this.resolveParam<ResolvedNumberParam>("complex")
            .default(() => {
                return { output: positiveDefaultValue };
            })
            .validate([(value) => value.output! >= 0, "be non-negative"]);

        readonly inserted = this.insertParam<boolean>(
            () => true
        ).noValidationNeeded();
    }

    test(`\`ParamsResolver\` with mixed value: success`, () => {
        const paramsResolver = new MixedParamsResolver();
        const resolutionResult = paramsResolver.resolve({
            input: positiveInputValue,
            complex: undefined,
            extra: "will not be resolved",
        });

        expect(resolutionResult.resolved).not.toBeNullish();
        expect(resolutionResult.resolved).toEqual({
            output: positiveInputValue,
            complex: {
                output: positiveDefaultValue,
            },
            inserted: true,
        });

        expect(resolutionResult.resolutionLogs).toHaveLength(3);
        const [outputLog, complexLog, insertedLog] =
            resolutionResult.resolutionLogs;

        expectParamResolutionResult(
            outputLog,
            {
                resultValue: positiveInputValue,
                inputReadCorrectly: {
                    wasPerformed: true,
                    withValue: positiveInputValue,
                },
            },
            "input"
        );
        expectParamResolutionResult(
            complexLog,
            {
                resultValue: {
                    output: positiveDefaultValue,
                },
                resolvedWithDefault: {
                    wasPerformed: true,
                    withValue: {
                        output: positiveDefaultValue,
                    },
                },
            },
            "complex"
        );
        expectParamResolutionResult(
            insertedLog,
            {
                resultValue: true,
                overriden: {
                    wasPerformed: true,
                    withValue: true,
                },
            },
            undefined
        );
    });

    test("`ParamsResolver` with mixed values: failure", () => {
        const paramsResolver = new MixedParamsResolver();
        const resolutionResult = paramsResolver.resolve({
            input: undefined,
            complex: {
                output: negativeInputValue,
            },
            extra: "will not be resolved",
        });

        expect(resolutionResult.resolved).toBeNullish();

        expect(resolutionResult.resolutionLogs).toHaveLength(3);
        const [outputLog, complexLog, insertedLog] =
            resolutionResult.resolutionLogs;

        expectParamResolutionResult(
            outputLog,
            {
                isInvalidCause:
                    "neither a user value nor a default one is specified",
            },
            "input"
        );
        expectParamResolutionResult(
            complexLog,
            {
                isInvalidCause: "should be non-negative, but has value",
                inputReadCorrectly: {
                    wasPerformed: true,
                    withValue: {
                        output: negativeInputValue,
                    },
                },
            },
            "complex"
        );
        expectParamResolutionResult(
            insertedLog,
            {
                resultValue: true,
                overriden: {
                    wasPerformed: true,
                    withValue: true,
                },
            },
            undefined
        );
    });

    class ParamsResolverWithNonResolverProperty extends NumberParamResolver {
        readonly nonResolverProperty: string = "i'm not a resolver!";
    }

    class ParamsResolverWithUnfinishedBuilder extends NumberParamResolver {
        readonly unfinishedBuilder = this.resolveParam<number>(
            "input"
        ).override(() => 6);
    }

    class ParamsResolverWithNonCertifiedResolverProperty extends NumberParamResolver {
        readonly nonCertifiedResolver = {
            resolve() {},
        };
    }

    test("`ParamsResolver` configured incorrectly: property of non-`ParamsResolver` type", () => {
        expect(() =>
            new ParamsResolverWithNonResolverProperty().resolve({
                input: positiveInputValue,
            })
        ).toThrow(Error, "configured incorrectly");
        expect(() =>
            new ParamsResolverWithUnfinishedBuilder().resolve({
                input: positiveInputValue,
            })
        ).toThrow(Error, "configured incorrectly");
        expect(() =>
            new ParamsResolverWithNonCertifiedResolverProperty().resolve({
                input: positiveInputValue,
            })
        ).toThrow(Error, "configured incorrectly");
    });

    class EmptyParamsResolver extends ParamsResolverImpl<
        InputNumberParam,
        ResolvedNumberParam
    > {
        constructor() {
            super(resolvedNumberParamSchema, "ResolvedNumberParam");
        }
    }

    test("`ParamsResolver` configured incorrectly: not enough parameters", () => {
        const paramsResolver = new EmptyParamsResolver();
        expect(() =>
            paramsResolver.resolve({
                input: positiveInputValue,
            })
        ).toThrow(Error, "configured incorrectly");
    });

    class WrongTypeParamsResolver extends ParamsResolverImpl<
        InputNumberParam,
        ResolvedNumberParam
    > {
        constructor() {
            super(resolvedNumberParamSchema, "ResolvedNumberParam");
        }

        output = this.resolveParam<string>("input")
            .default(() => "string type is the wrong one")
            .noValidationNeeded();
    }

    test("`ParamsResolver` configured incorrectly: parameter of wrong type", () => {
        const paramsResolver = new WrongTypeParamsResolver();
        expect(() =>
            paramsResolver.resolve({
                input: undefined,
            })
        ).toThrow(Error, "configured incorrectly");
    });

    interface InputParamsWithNestedParam {
        nestedParam?: InputNumberParam;
    }

    interface ResolvedParamsWithNestedParam {
        resolvedNestedParam: ResolvedNumberParam;
    }

    const resolvedParamsWithNestedParamSchema: JSONSchemaType<ResolvedParamsWithNestedParam> =
        {
            type: "object",
            properties: {
                resolvedNestedParam: {
                    type: "object",
                    oneOf: [resolvedNumberParamSchema],
                },
            },
            required: ["resolvedNestedParam"],
        };

    class ParamsResolverWithNestedResolver extends ParamsResolverImpl<
        InputParamsWithNestedParam,
        ResolvedParamsWithNestedParam
    > {
        constructor() {
            super(
                resolvedParamsWithNestedParamSchema,
                "ResolvedParamsWithNestedParam"
            );
        }

        readonly resolvedNestedParam = this.resolveNestedParams(
            "nestedParam",
            new NumberParamResolver()
        );
    }

    testSuccessfulSingleNumberResolution(
        "Test `resolveNestedParams`: basic, success",
        new ParamsResolverWithNestedResolver(),
        {
            nestedParam: {
                input: positiveInputValue,
            },
        },
        {
            resolvedNestedParam: {
                output: positiveInputValue,
            },
        },
        "nestedParam.input"
    );

    testFailedSingleNumberResolution(
        "Test `resolveNestedParams`: basic, failure",
        new ParamsResolverWithNestedResolver(),
        {
            nestedParam: {
                input: negativeInputValue,
            },
        },
        "nestedParam.input"
    );

    interface InputParamsWithDeepNestedParam {
        deepNestedParam?: InputParamsWithNestedParam;
    }

    interface ResolvedParamsWithDeepNestedParam {
        resolvedDeepNestedParam: ResolvedParamsWithNestedParam;
    }

    class ParamsResolverWithDeepNestedResolver extends ParamsResolverImpl<
        InputParamsWithDeepNestedParam,
        ResolvedParamsWithDeepNestedParam
    > {
        constructor() {
            super(
                {
                    type: "object",
                    properties: {
                        resolvedDeepNestedParam: {
                            type: "object",
                            oneOf: [resolvedParamsWithNestedParamSchema],
                        },
                    },
                    required: ["resolvedDeepNestedParam"],
                },
                "ResolvedParamsWithDeepNestedParam"
            );
        }

        readonly resolvedDeepNestedParam = this.resolveNestedParams(
            "deepNestedParam",
            new ParamsResolverWithNestedResolver()
        );
    }

    testSuccessfulSingleNumberResolution(
        "Test `resolveNestedParams`: deep nesting & all defined, success",
        new ParamsResolverWithDeepNestedResolver(),
        {
            deepNestedParam: {
                nestedParam: {
                    input: positiveInputValue,
                },
            },
        },
        {
            resolvedDeepNestedParam: {
                resolvedNestedParam: {
                    output: positiveInputValue,
                },
            },
        },
        "deepNestedParam.nestedParam.input"
    );

    test("Test `resolveNestedParams`: deep nesting & undefined in the middle, success", () => {
        const resolutionResult =
            new ParamsResolverWithDeepNestedResolver().resolve({
                deepNestedParam: {
                    nestedParam: undefined,
                },
            });
        expect(resolutionResult.resolved).toEqual({
            resolvedDeepNestedParam: {
                resolvedNestedParam: {
                    output: positiveDefaultValue,
                },
            },
        });
        expect(resolutionResult.resolutionLogs).toHaveLength(1);
        expectParamResolutionResult(
            resolutionResult.resolutionLogs[0],
            {
                resultValue: positiveDefaultValue,
                resolvedWithDefault: {
                    wasPerformed: true,
                    withValue: positiveDefaultValue,
                },
            },
            "deepNestedParam.nestedParam.input"
        );
    });

    testFailedSingleNumberResolution(
        "Test `resolveNestedParams`: deep nesting, failure",
        new ParamsResolverWithDeepNestedResolver(),
        {
            deepNestedParam: {
                nestedParam: {
                    input: negativeInputValue,
                },
            },
        },
        "deepNestedParam.nestedParam.input"
    );

    type ModelParamsHasNoOptionalProperties = [
        NoOptionalProperties<ModelParams>,
    ] extends [never]
        ? "false"
        : "true";

    type UserModelParamsHasNoOptionalProperties = [
        NoOptionalProperties<UserModelParams>,
    ] extends [never]
        ? "false"
        : "true";

    test("Test `NoOptionalProperties` constraint", () => {
        // @ts-ignore variable is needed only for a type check
        const _shouldBeTrue: ModelParamsHasNoOptionalProperties = "true";
        // @ts-ignore variable is needed only for a type check
        const _shouldBeFalse: UserModelParamsHasNoOptionalProperties = "false";
    });

    // The following code snippets should not compile (after adding required imports). Uncomment them to test.

    // class ResolveToTypeHasOptionalProperties extends ParamsResolverImpl<
    //     UserModelParams,
    //     UserModelParams
    // > {
    //     constructor() {
    //         super(userModelParamsSchema, "UserModelParams");
    //     }
    // }

    // class AttemptToSpecifyNonExistingPropertyOfInputType extends ParamsResolverImpl<
    //     UserModelParams,
    //     ModelParams
    // > {
    //     constructor() {
    //         super(modelParamsSchema, "ModelParams");
    //     }

    //     readonly unicorn = this.resolveParam<string>("unicorn")
    //         .requiredToBeConfigured()
    //         .noValidationNeeded();
    // }
});
