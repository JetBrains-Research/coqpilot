export function translateToSafeFileName(text: string): string {
    return text.replace(/[_ &\/\\#,+()$~%.'":*?<>{}]/g, "-").toLowerCase();
}

export function addJsonExtension(fileName: string): string {
    return `${fileName}.json`;
}

export function buildSafeJsonFileName(text: string): string {
    return addJsonExtension(translateToSafeFileName(text));
}
