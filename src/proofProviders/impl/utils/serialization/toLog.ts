import { JsonSpacing, toJsonString } from "../../../../utils/printers";

export function toOneLineLogString(
    shortName: string,
    providerData: any,
    verbose: boolean
): string {
    const proofProviderParamsString =
        providerData === undefined || !verbose
            ? ""
            : ` ${toJsonString(providerData, JsonSpacing.UNFORMATTED)}`;
    return `${shortName}${proofProviderParamsString}`;
}
