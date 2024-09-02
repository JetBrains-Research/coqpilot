import { any } from "./listUtils";
import { getOrPut } from "./mapUtils";

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
            elements.map((element) => JSON.stringify(element)).join()
        );
    }
}

export class EqualitySet<T extends EqualTo<T>> {
    private readonly hashToElements: Map<number, T[]> = new Map();
    private currentSize: number = 0;

    constructor(elements: T[] = []) {
        this.addElements(elements);
    }

    size(): number {
        return this.currentSize;
    }

    isEmpty(): boolean {
        return this.size() === 0;
    }

    has(element: T): boolean {
        const cell = this.hashToElements.get(element.hash());
        if (cell === undefined) {
            return false;
        }
        return any(cell, (other) => element.equalTo(other));
    }

    add(element: T): boolean {
        const cell = getOrPut(
            this.hashToElements,
            element.hash(),
            () => [] as T[]
        );
        if (any(cell, (other) => element.equalTo(other))) {
            return false;
        }
        cell.push(element);
        this.currentSize += 1;
        return true;
    }

    addElements(elements: T[]) {
        for (const element of elements) {
            this.add(element);
        }
    }

    elements(): T[] {
        return Array.from(this.hashToElements.values()).flat();
    }
}
