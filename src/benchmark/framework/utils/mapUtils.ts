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
