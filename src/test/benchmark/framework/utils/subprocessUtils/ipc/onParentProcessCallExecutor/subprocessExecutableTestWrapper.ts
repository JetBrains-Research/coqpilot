/**
 * Note: `subprocessName` should not contain any symbols
 * that might be interpreted as regex special symbols.
 */
export function subprocessExecutable(
    subprocessName: string,
    executable: () => Promise<any>
) {
    const testSuiteName = getSubprocessExecutableSuiteName(subprocessName);
    suite(testSuiteName, () => {
        test(subprocessName, async () => {
            await executable();
        });
    });
}

/**
 * @returns test-suite name to pass to `npm run test-executables-unsafe` via `--g` flag to execute the subprocess.
 */
export function getSubprocessExecutableSuiteName(
    subprocessName: string
): string {
    return `[SubprocessExecutable] ${subprocessName}`;
}
