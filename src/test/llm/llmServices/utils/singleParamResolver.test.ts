import { expect } from "earl";

import {
    ParamsResolver,
    SingleParamResolver,
} from "../../../../llm/llmServices/utils/paramsResolvers/abstractResolvers";
import { ResolutionActionResult } from "../../../../llm/llmServices/utils/paramsResolvers/abstractResolvers";
import {
    SingleParamResolverBuilder,
    ValidationRules,
    newParam,
    resolveParam,
} from "../../../../llm/llmServices/utils/paramsResolvers/builders";

import {
    ResolutionResultAddOns,
    expectParamResolutionResult,
} from "../../llmSpecificTestUtils/expectResolutionResult";

suite("[LLMService-s utils] Test single parameter resolution", () => {
    const inputParamName = "inputParam";

    interface InputParams<T> {
        inputParam: T | undefined;
    }

    function testSingleParamResolution<T>(
        testName: string,
        inputValue: T | undefined,
        buildResolver: (
            builder: SingleParamResolverBuilder<InputParams<T>, T>
        ) => SingleParamResolver<InputParams<T>, T>,
        expectedDefinedValues: ResolutionResultAddOns<T>
    ) {
        test(testName, () => {
            const paramResolverBuilder = resolveParam<InputParams<T>, T>(
                inputParamName
            );
            const paramResolver = buildResolver(paramResolverBuilder);
            const resolutionResult = paramResolver.resolveParam({
                inputParam: inputValue,
            });
            expectParamResolutionResult(
                resolutionResult,
                expectedDefinedValues,
                inputParamName
            );
        });
    }

    testSingleParamResolution<boolean>(
        "Test required param: value is specified",
        false,
        (builder) => builder.requiredToBeConfigured().noValidationNeeded(),
        {
            resultValue: false,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: false,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test required param: no value specified",
        undefined,
        (builder) => builder.requiredToBeConfigured().noValidationNeeded(),
        {
            isInvalidCause:
                "neither a user value nor a default one is specified",
        }
    );

    testSingleParamResolution<number>(
        "Test required param: value of wrong type is specified, but there is nothing we can do",
        "definitely not a number" as any,
        (builder) => builder.requiredToBeConfigured().noValidationNeeded(),
        {
            resultValue: "definitely not a number" as any,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: "definitely not a number" as any,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test resolution with default: value is already defined",
        false,
        (builder) => builder.default(() => true).noValidationNeeded(),
        {
            resultValue: false,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: false,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test resolution with default: resolved with default",
        undefined,
        (builder) => builder.default(() => true).noValidationNeeded(),
        {
            resultValue: true,
            resolvedWithDefault: {
                wasPerformed: true,
                withValue: true,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test resolution with default: failed",
        undefined,
        (builder) =>
            builder
                .default(
                    (inputParams) =>
                        inputParams.inputParam !== undefined ? true : undefined,
                    "Please configure the parameter with a value other than `undefined`."
                )
                .noValidationNeeded(),
        {
            isInvalidCause:
                "Please configure the parameter with a value other than `undefined`.",
            resolvedWithDefault: {
                wasPerformed: true,
                withValue: undefined,
            },
        }
    );

    (
        [
            [false, "specified value"],
            [undefined, "no value specified"],
        ] as [boolean | undefined, string][]
    ).forEach(([value, testCaseName]) => {
        const inputReadCorrectly: ResolutionActionResult<boolean> =
            value === undefined
                ? { wasPerformed: false }
                : { wasPerformed: true, withValue: value };

        testSingleParamResolution<boolean>(
            `Test override with "always true": ${testCaseName} overriden`,
            value,
            (builder) =>
                builder
                    .override(() => true, "is always true")
                    .requiredToBeConfigured()
                    .noValidationNeeded(),
            {
                resultValue: true,
                inputReadCorrectly: inputReadCorrectly,
                overriden: {
                    wasPerformed: true,
                    withValue: true,
                    message: "is always true",
                },
            }
        );

        testSingleParamResolution<boolean>(
            `Test override with mock: ${testCaseName} overriden`,
            value,
            (builder) => builder.overrideWithMock(() => true),
            { resultValue: true, inputReadCorrectly: inputReadCorrectly }
        );
    });

    (
        [
            [5, "specified value overriden", 6],
            [undefined, "no value specified resolved with default", 1],
            [0, "specified value is forced to be resolved with default", 1],
        ] as [number | undefined, string, number][]
    ).forEach(([value, testCaseName, expectedResultValue]) => {
        const overriderMessage =
            "is 6 if value is defined and non-zero; otherwise should be resolved with default";
        const shouldNotOverride = value === undefined || value === 0;
        testSingleParamResolution<number>(
            `Test conditional override with default resolution: ${testCaseName}`,
            value,
            (builder) =>
                builder
                    .override(() => {
                        if (shouldNotOverride) {
                            return undefined;
                        }
                        return 6;
                    }, overriderMessage)
                    .default(() => 1)
                    .noValidationNeeded(),
            {
                resultValue: expectedResultValue,
                inputReadCorrectly: {
                    wasPerformed: value === undefined ? false : true,
                    withValue: value,
                },
                overriden: {
                    wasPerformed: true,
                    withValue: shouldNotOverride ? undefined : 6,
                    message: overriderMessage,
                },
                resolvedWithDefault: {
                    wasPerformed: shouldNotOverride ? true : false,
                    withValue: shouldNotOverride ? 1 : undefined,
                },
            }
        );
    });

    testSingleParamResolution<boolean>(
        "Test param validation: 1 rule, success",
        true,
        (builder) =>
            builder
                .requiredToBeConfigured()
                .validate([(value) => value, "be true"]),
        {
            resultValue: true,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: true,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test param validation: 1 rule, failure",
        false,
        (builder) =>
            builder
                .requiredToBeConfigured()
                .validate([(value) => value, "be true"]),
        {
            isInvalidCause: "should be true, but has value",
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: false,
            },
        }
    );

    testSingleParamResolution<number>(
        "Test param validation: multiple rules, success",
        5,
        (builder) =>
            builder
                .requiredToBeConfigured()
                .validate(
                    [(value) => value > 0, "be positive"],
                    [(value) => value < 100, "be less than 100"]
                ),
        {
            resultValue: 5,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: 5,
            },
        }
    );

    testSingleParamResolution<number>(
        "Test param validation: multiple rules, first fails",
        -5,
        (builder) =>
            builder
                .requiredToBeConfigured()
                .validate(
                    [(value) => value > 0, "be positive"],
                    [(value) => value < 100, "be less than 100"]
                ),
        {
            isInvalidCause: "should be positive, but has value",
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: -5,
            },
        }
    );

    testSingleParamResolution<boolean>(
        "Test validate at runtime: pass",
        true,
        (builder) => builder.requiredToBeConfigured().validateAtRuntimeOnly(),
        {
            resultValue: true,
            inputReadCorrectly: {
                wasPerformed: true,
                withValue: true,
            },
        }
    );

    test("Test dot notation: success", () => {
        const inputParams = {
            complexParam: {
                inputParam: true,
            },
        };
        const complexParamName = "complexParam.inputParam";
        const paramResolver = resolveParam(complexParamName)
            .requiredToBeConfigured()
            .noValidationNeeded();
        const resolutionResult = paramResolver.resolveParam(inputParams);
        expectParamResolutionResult(
            resolutionResult,
            {
                resultValue: true,
                inputReadCorrectly: {
                    wasPerformed: true,
                    withValue: true,
                },
            },
            complexParamName
        );
    });

    test("Test no property with such name: always returns no value specified", () => {
        const inputParams = {
            complexParam: {
                inputParam: true,
            },
        };
        [
            "unknownParam",
            "complexParam.unknownParam",
            "unknownParam.unknownParam",
        ].forEach((unknownParamName) => {
            expectParamResolutionResult(
                resolveParam(unknownParamName)
                    .requiredToBeConfigured()
                    .noValidationNeeded()
                    .resolveParam(inputParams),
                {
                    isInvalidCause:
                        "neither a user value nor a default one is specified",
                },
                unknownParamName
            );
        });
    });

    test("Test `newParam`: success", () => {
        const paramResolver = newParam<InputParams<boolean>, number>(
            () => 5
        ).noValidationNeeded();
        const inputParams = {
            inputParam: false,
        };
        const resolutionResult = paramResolver.resolveParam(inputParams);
        expectParamResolutionResult(
            resolutionResult,
            {
                resultValue: 5,
                overriden: {
                    wasPerformed: true,
                    withValue: 5,
                },
            },
            undefined
        );
    });

    test("Test builders return `SingleParamResolver` as valid `ParamsResolver`", () => {
        const paramResolver = resolveParam<InputParams<number>, number>(
            inputParamName
        )
            .requiredToBeConfigured()
            .validate(ValidationRules.bePositiveNumber) as ParamsResolver<
            InputParams<number>,
            number
        >;

        const successResult = paramResolver.resolve({
            inputParam: 5,
        });
        expect(successResult.resolved).toEqual(5);
        expect(successResult.resolutionLogs).toHaveLength(1);
        expectParamResolutionResult(
            successResult.resolutionLogs[0],
            {
                resultValue: 5,
                inputReadCorrectly: {
                    wasPerformed: true,
                    withValue: 5,
                },
            },
            inputParamName
        );

        const failureResult = paramResolver.resolve({
            inputParam: -5,
        });
        expect(failureResult.resolved).toBeNullish();
        expect(failureResult.resolutionLogs).toHaveLength(1);
        expectParamResolutionResult(
            failureResult.resolutionLogs[0],
            {
                inputReadCorrectly: {
                    wasPerformed: true,
                    withValue: -5,
                },
                isInvalidCause: "should be positive, but has value",
            },
            inputParamName
        );
    });
});
