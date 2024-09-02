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
