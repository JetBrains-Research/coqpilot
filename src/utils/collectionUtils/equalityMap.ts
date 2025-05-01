import { EqualTo } from "./equalityUtils";
import { getOrPut } from "./mapUtils";

export interface Entry<K, V> {
    key: K;
    value: V;
}

export class EqualityMap<K extends EqualTo<K>, V> {
    private readonly hashToEntries: Map<number, Entry<K, V>[]> = new Map();
    private currentSize: number = 0;

    constructor(entries: [K, V][] = []) {
        this.setEntries(entries);
    }

    size(): number {
        return this.currentSize;
    }

    isEmpty(): boolean {
        return this.size() === 0;
    }

    has(key: K): boolean {
        const [_, targetEntry] = this.getCellAndEntry(key, false);
        return targetEntry === undefined;
    }

    get(key: K): V | undefined {
        const [_, targetEntry] = this.getCellAndEntry(key, false);
        return targetEntry?.value;
    }

    getOrPut(key: K, valueToPutIfAbsent: () => V): V {
        const value = this.get(key);
        if (value === undefined) {
            const newValue = valueToPutIfAbsent();
            this.set(key, newValue);
            return newValue;
        } else {
            return value;
        }
    }

    /**
     * @returns true if the key was already present, false otherwise.
     */
    set(key: K, value: V): boolean {
        const [cell, targetEntry] = this.getCellAndEntry(key, true);
        if (targetEntry === undefined) {
            cell!.push({ key, value });
            this.currentSize += 1;
            return false;
        } else {
            targetEntry.value = value;
            return true;
        }
    }

    setEntries(entries: [K, V][]) {
        for (const [key, value] of entries) {
            this.set(key, value);
        }
    }

    entries(): Entry<K, V>[] {
        return Array.from(this.hashToEntries.values()).flat();
    }

    private getCellAndEntry(
        key: K,
        putCellIfAbsent: boolean
    ): [Entry<K, V>[] | undefined, Entry<K, V> | undefined] {
        let cell: Entry<K, V>[] | undefined;
        if (putCellIfAbsent) {
            cell = getOrPut(
                this.hashToEntries,
                key.hash(),
                () => [] as Entry<K, V>[]
            );
        } else {
            cell = this.hashToEntries.get(key.hash());
        }
        return [cell, cell?.find((entry) => key.equalTo(entry.key))];
    }
}
