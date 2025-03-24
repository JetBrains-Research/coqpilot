export function translateToSafeFileName(text: string): string {
    return text.replace(/[_ &\/\\#,+()$~%.'":*?<>{}]/g, "-").toLowerCase();
}

export function addExtension(fileName: string, extension: string): string {
    return `${fileName}${extension}`;
}

export function addJsonExtension(fileName: string): string {
    return `${fileName}.json`;
}

export function buildSafeJsonFileName(text: string): string {
    return addJsonExtension(translateToSafeFileName(text));
}
