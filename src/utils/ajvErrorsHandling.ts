import Ajv, { DefinedError, Options } from "ajv";

import { stringifyDefinedValue } from "./printers";

export enum AjvMode {
    RETURN_AFTER_FIRST_ERROR,
    COLLECT_ALL_ERRORS,
}

export function buildAjv(mode: AjvMode): Ajv {
    const ajvOptions: Options =
        mode === AjvMode.RETURN_AFTER_FIRST_ERROR ? {} : { allErrors: true };
    return new Ajv(ajvOptions);
}

export function ajvErrorsAsString(
    errorObjects: DefinedError[],
    ignoreErrorsWithKeywords: string[] = []
) {
    const errorsToReport = errorObjects.filter(
        (errorObject) => !ignoreErrorsWithKeywords.includes(errorObject.keyword)
    );
    return errorsToReport.map((error) => stringifyAjvError(error)).join("; ");
}

export function stringifyAjvError(error: DefinedError): string {
    // To support more keywords, check https://ajv.js.org/api.html#error-parameters.
    switch (error.keyword) {
        case "required":
            return `required property ${buildQualifiedPropertyName(error.instancePath, error.params.missingProperty)} is missing`;
        case "additionalProperties":
            return `unknown property ${buildQualifiedPropertyName(error.instancePath, error.params.additionalProperty)}`;
        case "type":
            return `${buildQualifiedPropertyName(error.instancePath)} property must be of type "${error.params.type}"`;
        case "oneOf":
            return `${buildQualifiedPropertyName(error.instancePath)} property must match exactly one of the specified schemas`;
        default:
            return stringifyDefinedValue(error);
    }
}

function buildQualifiedPropertyName(
    instancePath: string,
    propertySimpleName?: string
): string {
    const qualifiedPath = (
        instancePath.startsWith("/") ? instancePath.substring(1) : instancePath
    ).replace("/", ".");
    const name = propertySimpleName === undefined ? "" : propertySimpleName;
    return qualifiedPath !== "" && name !== ""
        ? `\`${qualifiedPath}.${name}\``
        : `\`${qualifiedPath}${name}\``;
}
