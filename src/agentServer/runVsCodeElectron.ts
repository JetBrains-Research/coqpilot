import { runTests } from "@vscode/test-electron";
import * as path from "path";

async function main() {
    try {
        const args = process.argv.slice(2);
        const envVals = args.reduce(
            (acc, arg) => {
                const [key, val] = arg.split("=");
                acc[key] = val;
                return acc;
            },
            {} as { [key: string]: string | undefined }
        );
        const extensionDevelopmentPath = path.resolve(__dirname, "../../");
        const extensionTestsPath = path.resolve(__dirname, "./boot");

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
