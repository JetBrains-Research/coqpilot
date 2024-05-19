import { stringifyAnyValue } from "../../../../utils/printers";

export function accessParamByName<InputType>(
    inputParams: InputType,
    inputParamNameInDotNotation: string,
    throwOnUndefinedInterimProperty: boolean = false
): any {
    const propertiesNames = inputParamNameInDotNotation.split(".");
    let accessedProperty: any = inputParams;
    for (const propertyName of propertiesNames) {
        const accessKey = propertyName as keyof typeof accessedProperty;
        if (
            accessedProperty === undefined ||
            accessedProperty === null ||
            accessKey === null
        ) {
            if (throwOnUndefinedInterimProperty) {
                throw Error(
                    `failed to access \`${inputParams}\` property in ${stringifyAnyValue(inputParams)} input params`
                );
            } else {
                return undefined;
            }
        }
        accessedProperty = accessedProperty[accessKey];
    }
    return accessedProperty;
}
