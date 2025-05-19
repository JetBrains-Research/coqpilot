export const FILES_TO_TEST_LAST = [
    /**
     * Since this tests interact with VSCode UI,
     * it's safer to run them after all other tests have been finished.
     */
    "extension/coqPilot.test.js",
];

export function orderTestFiles(allTestFilesPaths: string[]): string[] {
    const filesWithoutLast = allTestFilesPaths.filter(
        (filePath) => FILES_TO_TEST_LAST.indexOf(filePath) === -1
    );
    const orderedFiles = [...filesWithoutLast, ...FILES_TO_TEST_LAST];
    return orderedFiles;
}
