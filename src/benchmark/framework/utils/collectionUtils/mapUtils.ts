import { stringifyAnyValue } from "../../../../utils/printers";
import { illegalState } from "../../../../utils/throwErrors";

import { EqualityMap } from "./equalityMap";
import { EqualTo } from "./equalityUtils";

export function getOrPut<K, V, M extends Map<K, V>>(
    map: M,
    key: K,
    valueToPutIfAbsent: () => V
): V {
    if (map.has(key)) {
        return map.get(key)!;
    }
    const value = valueToPutIfAbsent();
    map.set(key, value);
    return value;
}

export function getOrThrow<K, V, M extends Map<K, V>>(
    map: M,
    key: K,
    errorMessage: string
): V {
    const value = map.get(key);
    if (value === undefined) {
        illegalState(errorMessage);
    }
    return value;
}

export function groupByAndMap<T, K, V>(
    elements: T[],
    keyExtractor: (element: T) => K,
    valueMapper: (element: T) => V
): Map<K, V[]> {
    const resultMap = new Map<K, V[]>();
    for (const element of elements) {
        const key = keyExtractor(element);
        const values = getOrPut<K, V[], Map<K, V[]>>(resultMap, key, () => []);
        values.push(valueMapper(element));
    }
    return resultMap;
}

export function groupBy<T, K>(
    elements: T[],
    keyExtractor: (element: T) => K
): Map<K, T[]> {
    return groupByAndMap(elements, keyExtractor, (element) => element);
}

export function groupByToEqualityMap<T, K extends EqualTo<K>, V>(
    elements: T[],
    keyExtractor: (element: T) => K,
    valueMapper: (element: T) => V
): EqualityMap<K, V[]> {
    const resultMap = new EqualityMap<K, V[]>();
    for (const element of elements) {
        const key = keyExtractor(element);
        const values = resultMap.getOrPut(key, () => []);
        values.push(valueMapper(element));
    }
    return resultMap;
}

export function mapValues<K, V, M extends Map<K, V>, T>(
    map: M,
    buildNewValue: (key: K, value: V) => T
): Map<K, T> {
    const resultMap = new Map<K, T>();
    for (const [key, value] of map.entries()) {
        resultMap.set(key, buildNewValue(key, value));
    }
    return resultMap;
}

function reduceToMapImpl<T, K, V>(
    elements: T[],
    keyExtractor: (element: T) => K | undefined,
    valueMapper: (element: T) => V | undefined,
    onRepeatedKey: (key: K) => void
): Map<K, V> {
    const resultMap = new Map<K, V>();
    for (const element of elements) {
        const key = keyExtractor(element);
        if (key === undefined) {
            continue;
        }
        if (resultMap.has(key)) {
            onRepeatedKey(key);
            continue;
        }
        const value = valueMapper(element);
        if (value === undefined) {
            continue;
        }
        resultMap.set(key, value);
    }
    return resultMap;
}

export function reduceToMap<T, K, V>(
    elements: T[],
    keyExtractor: (element: T) => K | undefined,
    valueMapper: (element: T) => V | undefined
): Map<K, V> {
    return reduceToMapImpl(elements, keyExtractor, valueMapper, () => {});
}

export function packIntoMap<T, K, V>(
    elements: T[],
    keyExtractor: (element: T) => K | undefined,
    valueMapper: (element: T) => V | undefined
): Map<K, V> {
    return reduceToMapImpl(elements, keyExtractor, valueMapper, (key) =>
        illegalState(
            `Cannot pack elements into a map since keys are not unique: ${stringifyAnyValue(key)}`
        )
    );
}

export function packIntoMappedObject<T, V>(
    elements: T[],
    keyExtractor: (element: T) => string | undefined,
    valueMapper: (element: T) => V | undefined
): { [key: string]: V } {
    const mappedObject: { [key: string]: V } = {};
    for (const element of elements) {
        const key = keyExtractor(element);
        const value = valueMapper(element);
        if (key === undefined || value === undefined) {
            continue;
        }
        mappedObject[key] = value;
    }
    return mappedObject;
}

export function toMappedObject<V, M extends Map<string, V>>(
    map: M
): { [key: string]: V } {
    return entriesToMappedObject(Array.from(map.entries()));
}

export function entriesToMappedObject<V>(entries: [string, V][]): {
    [key: string]: V;
} {
    const mappedObject: { [key: string]: V } = {};
    for (const [key, value] of entries) {
        mappedObject[key] = value;
    }
    return mappedObject;
}

export function fromMappedObject<V>(mappedObject: {
    [key: string]: V;
}): Map<string, V> {
    return new Map(mappedObjectEntries(mappedObject));
}

export function mappedObjectEntries<V>(mappedObject: {
    [key: string]: V;
}): [string, V][] {
    const entries: [string, V][] = [];
    for (const key in mappedObject) {
        entries.push([key, mappedObject[key]]);
    }
    return entries;
}

export function mappedObjectValues<V>(mappedObject: { [key: string]: V }): V[] {
    const values: V[] = [];
    for (const key in mappedObject) {
        values.push(mappedObject[key]);
    }
    return values;
}
