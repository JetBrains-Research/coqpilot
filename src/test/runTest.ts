import { runTests } from "@vscode/test-electron";
import * as path from "path";

async function main() {
    try {
        // The folder containing the Extension Manifest package.json
        // Passed to `--extensionDevelopmentPath`
        const extensionDevelopmentPath = path.resolve(__dirname, "../../");

        // The path to test runner
        // Passed to --extensionTestsPath
        const extensionTestsPath = path.resolve(__dirname, "./index");

        // Download VS Code, unzip it and run the integration test
        const args = process.argv.slice(2);
        const envVals = args.reduce(
            (acc, arg) => {
                const [key, val] = arg.split("=");
                acc[`TEST_ARG${key}`] = val;
                return acc;
            },
            {} as { [key: string]: string | undefined }
        );

        await runTests({
            extensionDevelopmentPath,
            extensionTestsPath,
            extensionTestsEnv: envVals,
        });
    } catch (err) {
        console.error("Failed to run tests", err);
        process.exit(1);
    }
}

main();
