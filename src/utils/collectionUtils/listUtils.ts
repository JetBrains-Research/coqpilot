import { invariantFailed } from "../errors/throwErrors";
import { stringifyAnyValue } from "../printers";

import { EqualitySet } from "./equalitySet";
import { EqualTo, HashUtils } from "./equalityUtils";

export function any<T>(
    elements: T[],
    condition: (element: T) => boolean
): boolean {
    return elements.findIndex(condition) !== -1;
}

export function all<T>(
    elements: T[],
    condition: (element: T) => boolean
): boolean {
    return !any(elements, reverseCondition(condition));
}

function reverseCondition<T>(
    condition: (element: T) => boolean
): (element: T) => boolean {
    return (element) => !condition(element);
}

export function lastElement<T extends Exclude<unknown, undefined | null>>(
    elements: T[]
): T | undefined {
    return elements[elements.length - 1];
}

export function removeElement(
    elements: string[],
    elementToRemove: string,
    onNoSuchElement: () => void = () => {}
) {
    const removedAtIndex = removeElementAndReturn(elements, elementToRemove);
    if (removedAtIndex === undefined) {
        onNoSuchElement();
    }
}

export function removeElementAndReturn(
    elements: string[],
    elementToRemove: string
): number | undefined {
    const index = elements.indexOf(elementToRemove);
    if (index !== -1) {
        elements.splice(index, 1);
        return index;
    } else {
        return undefined;
    }
}

export function makeElementsUnique<T extends EqualTo<T>>(elements: T[]) {
    return new EqualitySet(elements).elements();
}

export function makeElementsUniqueByStringKeys<T>(
    elements: T[],
    extractKey: (element: T) => string
): T[] {
    return makeAnyElementsUniqueImpl(
        elements,
        extractKey,
        (thisKey, otherKey) => thisKey === otherKey,
        (key) => HashUtils.hashString(key)
    );
}

export function makeStringsUnique(elements: string[]): string[] {
    return makeElementsUniqueByStringKeys(elements, (element) => element);
}

export function makeAnyElementsUnique<T>(
    elements: T[],
    equals: (thisElement: T, otherElement: T) => boolean,
    hash: (element: T) => number
): T[] {
    return makeAnyElementsUniqueImpl(
        elements,
        (element) => element,
        equals,
        hash
    );
}

function makeAnyElementsUniqueImpl<T, K>(
    elements: T[],
    extractKey: (element: T) => K,
    equals: (thisKey: K, otherKey: K) => boolean,
    hash: (key: K) => number
): T[] {
    class WrappedT implements EqualTo<WrappedT> {
        key: K;

        constructor(readonly element: T) {
            this.key = extractKey(element);
        }
        equalTo(other: WrappedT): boolean {
            return equals(this.key, other.key);
        }
        hash(): number {
            return hash(this.key);
        }
    }
    const set = new EqualitySet(
        elements.map((element) => new WrappedT(element))
    );
    return set.elements().map((wrappedElement) => wrappedElement.element);
}

export function findFirstDuplicate(xs: string[]): string | undefined {
    const uniqueXs = new Set<string>();
    for (const x of xs) {
        if (uniqueXs.has(x)) {
            return x;
        } else {
            uniqueXs.add(x);
        }
    }
    return undefined;
}

export function zip<T, V>(ts: T[], vs: V[]): [T, V][] {
    if (ts.length !== vs.length) {
        invariantFailed(
            "Zip function",
            "arrays should be of the same length, ",
            `but got ${stringifyAnyValue(ts)} and ${stringifyAnyValue(vs)}`
        );
    }
    return ts.map((t, i) => [t, vs[i]]);
}

export function printHeadTailItems<T>(
    headItemsNumber: number,
    tailItemsNumber: number,
    items: T[],
    printItem: (item: T) => string
): string {
    function itemsToString(selectedItems: T[]): string {
        return selectedItems.map(printItem).join(", ");
    }

    if (items.length <= headItemsNumber + tailItemsNumber) {
        return `[${itemsToString(items)}]`;
    }
    const firstKeys = items.slice(0, headItemsNumber);
    const lastKeys = items.slice(items.length - tailItemsNumber - 1);
    return `[${itemsToString(firstKeys)}, ..., ${itemsToString(lastKeys)}]`;
}
