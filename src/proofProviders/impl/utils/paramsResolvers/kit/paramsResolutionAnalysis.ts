import { stringifyAnyValue } from "../../../../../utils/printers";
import { ModelParams } from "../../../modelParams";
import {
    ParamsResolutionResult,
    SingleParamResolutionResult,
} from "../abstractResolvers";

export interface ParamsResolutionMessages {
    invalidConfigurationMessage?: string;
    warningMessage?: string;
}

export function buildParamsResolutionMessages<
    ResolvedModelParams extends ModelParams,
>(
    paramsResolutionResult: ParamsResolutionResult<ResolvedModelParams>,
    modelId: string
): ParamsResolutionMessages {
    const analyzedResolution = analyzeParamsResolution(paramsResolutionResult);
    const errors = analyzedResolution.errorMessages;
    const warnings = analyzedResolution.warningMessages;
    const messages: ParamsResolutionMessages = {};

    if (errors.length !== 0) {
        const intro = `Model "${modelId}" is configured incorrectly:`;
        messages.invalidConfigurationMessage = `${intro} ${errors.join(";")}.`;
    }

    if (warnings.length !== 0) {
        const intro = `Model "${modelId}" configuration is a subject to warnings.`;
        messages.warningMessage = `${intro} ${warnings.join(" ")}`;
    }

    return messages;
}

export interface AnalyzedParamsResolution {
    errorMessages: string[];
    warningMessages: string[];
}

export function analyzeParamsResolution<
    ResolvedModelParams extends ModelParams,
>(
    resolutionResult: ParamsResolutionResult<ResolvedModelParams>
): AnalyzedParamsResolution {
    const analyzedResolution: AnalyzedParamsResolution = {
        errorMessages: [],
        warningMessages: [],
    };
    for (const paramLog of resolutionResult.resolutionLogs) {
        const analyzedSingleParamResolution =
            analyzeSingleParamResolution(paramLog);
        analyzedResolution.errorMessages.push(
            ...analyzedSingleParamResolution.errorMessages
        );
        analyzedResolution.warningMessages.push(
            ...analyzedSingleParamResolution.warningMessages
        );
    }
    return analyzedResolution;
}

export function analyzeSingleParamResolution(
    paramLog: SingleParamResolutionResult<any>
): AnalyzedParamsResolution {
    const analyzedResolution: AnalyzedParamsResolution = {
        errorMessages: [],
        warningMessages: [],
    };

    const resolutionFailed = paramLog.resultValue === undefined;

    const inputNotReadCorrectly = !paramLog.inputReadCorrectly.wasPerformed;
    const inputValueWasDefined =
        paramLog.inputReadCorrectly.withValue !== undefined;

    const definedValueWasOverriden =
        paramLog.overriden.wasPerformed && inputValueWasDefined;
    const definedValueWasOverridenWithMock =
        paramLog.overridenWithMock.wasPerformed && inputValueWasDefined;

    const possibleWarnings =
        inputNotReadCorrectly ||
        definedValueWasOverriden ||
        definedValueWasOverridenWithMock;

    const cleanResolution = !resolutionFailed && !possibleWarnings;
    if (cleanResolution) {
        return analyzedResolution;
    }

    if (resolutionFailed) {
        const wrappedResolutionHistory =
            buildWrappedResolutionHistory(paramLog);
        analyzedResolution.errorMessages.push(
            `${paramLog.isInvalidCause}${wrappedResolutionHistory}`
        );
    }

    const paramName = paramLog.inputParamName ?? "<undefined parameter>";

    function addWarning(...message: string[]) {
        analyzedResolution.warningMessages.push(message.join(""));
    }

    if (inputNotReadCorrectly) {
        addWarning(
            `The \`${paramName}\` parameter was successfully resolved, `,
            `but the initial input value was not read correctly. `,
            "Please configure it properly or leave unspecified."
        );
    }

    function addDefinedValueWasOverridenWarning(
        withValue: any,
        explanation: string | undefined,
        mockValueWord: string
    ) {
        const wrappedExplanation =
            explanation === undefined
                ? ""
                : `, \`${paramName}\` ${explanation}`;
        addWarning(
            `The input value of the \`${paramName}\` parameter was overriden `,
            `with the ${mockValueWord} ${stringifyAnyValue(withValue)}${wrappedExplanation}. `,
            "Please configure it the same way or leave unspecified."
        );
    }

    if (definedValueWasOverriden) {
        addDefinedValueWasOverridenWarning(
            paramLog.overriden.withValue,
            paramLog.overriden.message,
            "value"
        );
    }
    if (definedValueWasOverridenWithMock) {
        addDefinedValueWasOverridenWarning(
            paramLog.overridenWithMock.withValue,
            undefined,
            "mock value"
        );
    }

    return analyzedResolution;
}

function buildWrappedResolutionHistory(
    paramLog: SingleParamResolutionResult<any>
): string {
    const resolutionHistory = buildResolutionHistory(paramLog);
    return resolutionHistory === ""
        ? ""
        : `; value's resolution: ${resolutionHistory}`;
}

export function buildResolutionHistory(
    paramLog: SingleParamResolutionResult<any>
): string {
    const inputReadPerformed = paramLog.inputReadCorrectly.wasPerformed;
    const overridePerformed = paramLog.overriden.wasPerformed;
    const overrideWithMockPerformed = paramLog.overridenWithMock.wasPerformed;
    const withDefaultPerformed = paramLog.resolvedWithDefault.wasPerformed;

    const onlySuccessfulRead =
        inputReadPerformed &&
        !overridePerformed &&
        !overrideWithMockPerformed &&
        !withDefaultPerformed;
    if (onlySuccessfulRead) {
        return "";
    }
    const inputRead =
        paramLog.inputReadCorrectly.withValue !== undefined
            ? `read ${stringifyAnyValue(paramLog.inputReadCorrectly.withValue)}`
            : "no input value read";
    const withOverride = paramLog.overriden.wasPerformed
        ? `, overriden with ${stringifyAnyValue(paramLog.overriden.withValue)}`
        : "";
    const withMockOverride = paramLog.overridenWithMock.wasPerformed
        ? `, overriden with mock ${stringifyAnyValue(paramLog.overriden.withValue)}`
        : "";
    const withDefault = paramLog.resolvedWithDefault.wasPerformed
        ? `, resolved with default ${stringifyAnyValue(paramLog.resolvedWithDefault.withValue)}`
        : "";
    const result =
        paramLog.resultValue === undefined
            ? ", result is unresolved"
            : `, result is ${stringifyAnyValue(paramLog.resultValue)}`;

    const invalidRead = !inputReadPerformed;
    const anyResolutionActionPerformed =
        overridePerformed || overrideWithMockPerformed || withDefaultPerformed;
    return invalidRead || anyResolutionActionPerformed
        ? `${inputRead}${withOverride}${withMockOverride}${withDefault}${result}`
        : "";
}
