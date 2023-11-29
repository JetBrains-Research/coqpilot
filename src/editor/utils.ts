/**
 * Add an indent to the beginning of each line of text, apart from the first.
 * @param text Text to format.
 * @param indent Number of spaces to indent.
 * @returns Formatted text.
 */
export function makeIndent(text: string, indent: number) {
    const indentStr = ' '.repeat(indent);
    return text.replace(/\n/g, '\n' + indentStr);
}