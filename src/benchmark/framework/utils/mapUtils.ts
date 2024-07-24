import { stringifyAnyValue } from "../../../utils/printers";

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

export function packIntoMap<T, K, V>(
    elements: T[],
    keyExtractor: (element: T) => K | undefined,
    valueMapper: (element: T) => V | undefined
): Map<K, V> {
    const resultMap = new Map<K, V>();
    for (const element of elements) {
        const key = keyExtractor(element);
        if (key === undefined) {
            continue;
        }
        if (resultMap.has(key)) {
            throw Error(
                `Cannot pack elements into a map since keys are not unique: ${stringifyAnyValue(key)}`
            );
        }
        const value = valueMapper(element);
        if (value === undefined) {
            continue;
        }
        resultMap.set(key, value);
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
