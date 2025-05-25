export function checkUITestsEnabled(): boolean {
    return !(process.env.DISABLE_UI_TESTS === "true");
}

export const UI_TESTS_DISABLED_CAUSE = `\`DISABLE_UI_TESTS\` is true`;
