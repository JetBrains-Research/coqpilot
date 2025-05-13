import { expect } from "earl";

import { SingleParamResolutionResult } from "../../../llm/llmServices/utils/paramsResolvers/abstractResolvers";

export type ResolutionResultAddOns<T> = Partial<SingleParamResolutionResult<T>>;

/**
 * All values of `actualResolutionResult` are checked for equality to
 * the corresponding values of the `expectedResolutionResult`,
 * except for the string ones: they are expected to include (!)
 * the corresponding values of the `expectedResolutionResult`.
 */
export function expectParamResolutionResult<T>(
    actualResolutionResult: SingleParamResolutionResult<T>,
    expectedNonDefaultValues: ResolutionResultAddOns<T>,
    inputParamName: string | undefined
) {
    const expectedResolutionResult = {
        inputParamName: inputParamName,
        resultValue: undefined,
        isInvalidCause: undefined,
        // `inputReadCorrectly` is false only if the input value is invalid
        inputReadCorrectly: {
            wasPerformed: true,
            withValue: undefined,
        },
        overriden: {
            wasPerformed: false,
            withValue: undefined,
            message: undefined,
        },
        overridenWithMock: {
            wasPerformed: false,
            withValue: undefined,
        },
        resolvedWithDefault: {
            wasPerformed: false,
            withValue: undefined,
        },
        ...expectedNonDefaultValues,
    };
    expect(actualResolutionResult.inputParamName).toEqual(
        expectedResolutionResult.inputParamName
    );
    expect(actualResolutionResult.resultValue).toEqual(
        expectedResolutionResult.resultValue
    );
    expectMessageValue(
        actualResolutionResult.isInvalidCause,
        expectedResolutionResult.isInvalidCause
    );
    expect(actualResolutionResult.inputReadCorrectly.wasPerformed).toEqual(
        expectedResolutionResult.inputReadCorrectly.wasPerformed
    );
    expect(actualResolutionResult.inputReadCorrectly.withValue).toEqual(
        expectedResolutionResult.inputReadCorrectly.withValue
    );
    expect(actualResolutionResult.overriden.wasPerformed).toEqual(
        expectedResolutionResult.overriden.wasPerformed
    );
    expect(actualResolutionResult.overriden.withValue).toEqual(
        expectedResolutionResult.overriden.withValue
    );
    expect(actualResolutionResult.overridenWithMock.wasPerformed).toEqual(
        expectedResolutionResult.overridenWithMock.wasPerformed
    );
    expect(actualResolutionResult.overridenWithMock.withValue).toEqual(
        expectedResolutionResult.overridenWithMock.withValue
    );
    expectMessageValue(
        actualResolutionResult.overriden.message,
        expectedResolutionResult.overriden.message
    );
    expect(actualResolutionResult.resolvedWithDefault.wasPerformed).toEqual(
        expectedResolutionResult.resolvedWithDefault.wasPerformed
    );
    expect(actualResolutionResult.resolvedWithDefault.withValue).toEqual(
        expectedResolutionResult.resolvedWithDefault.withValue
    );
}

export function expectMessageValue(
    actualMessage: string | undefined,
    expectedMessage: string | undefined
) {
    if (expectedMessage === undefined) {
        expect(actualMessage).toBeNullish();
    } else {
        expect(actualMessage).not.toBeNullish();
        expect(actualMessage!).toInclude(expectedMessage);
    }
}
