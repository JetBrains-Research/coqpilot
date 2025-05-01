import { EqualityMap } from "./equalityMap";
import { EqualTo } from "./equalityUtils";

export class EqualitySet<T extends EqualTo<T>> {
    private readonly map: EqualityMap<T, undefined> = new EqualityMap();

    constructor(elements: T[] = []) {
        this.addElements(elements);
    }

    size(): number {
        return this.map.size();
    }

    isEmpty(): boolean {
        return this.map.isEmpty();
    }

    has(element: T): boolean {
        return this.map.has(element);
    }

    add(element: T): boolean {
        return this.map.set(element, undefined);
    }

    addElements(elements: T[]) {
        for (const element of elements) {
            this.add(element);
        }
    }

    elements(): T[] {
        return this.map.entries().map((entry) => entry.key);
    }
}
