import { toUnformattedJsonString } from "../../../../utils/printers";

export interface EqualTo<T> {
    equalTo(other: T): boolean;

    hash(): number;
}

export namespace HashUtils {
    /**
     * Source: https://stackoverflow.com/a/7616484
     */
    export function hashString(text: string): number {
        var hash = 0,
            i,
            chr;
        if (text.length === 0) {
            return hash;
        }
        for (i = 0; i < text.length; i++) {
            chr = text.charCodeAt(i);
            hash = (hash << 5) - hash + chr;
            hash |= 0;
        }
        return hash;
    }

    export function hashAsStrings(...elements: any[]): number {
        return hashString(
            elements.map((element) => toUnformattedJsonString(element)).join()
        );
    }
}
