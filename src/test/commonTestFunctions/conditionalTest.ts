import { color } from "./colorPrinter";

export function testIf(
    condition: boolean,
    testWillBeSkippedCause: string,
    suiteName: string,
    testName: string,
    func: Mocha.Func
): Mocha.Test | undefined {
    if (condition) {
        return test(testName, func);
    }
    console.warn(
        `${color("WARNING", "yellow")}: test will be skipped: \"${suiteName}\" # \"${testName}\"\n\t> cause: ${testWillBeSkippedCause}`
    );
    return undefined;
}
