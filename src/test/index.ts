import { globSync } from "glob";
import * as Mocha from "mocha";
import * as path from "path";

import { orderTestFiles } from "./testsOrder";

export function run(): Promise<void> {
    // Create the mocha test
    const mocha = new Mocha({
        ui: "tdd",
        color: true,
        diff: true,
        grep: process.env["TEST_ARG-r"],
        fgrep: process.env["TEST_ARG-g"],
        invert: process.env["TEST_ARG-i"] === "true",
    });

    // Do not ignore unhandled rejected promises
    process.on("unhandledRejection", (err) => {
        throw err;
    });

    const testsRoot = path.resolve(__dirname);

    return new Promise((c, e) => {
        try {
            const files = globSync("**/**.test.js", { cwd: testsRoot });
            const orderedFiles = orderTestFiles(files);

            orderedFiles.forEach((f) =>
                mocha.addFile(path.resolve(testsRoot, f))
            );

            mocha.run((failures) => {
                if (failures > 0) {
                    e(Error(`${failures} tests failed.`));
                } else {
                    c();
                }
            });
        } catch (err) {
            console.error(err);
            e(err);
        }
    });
}
