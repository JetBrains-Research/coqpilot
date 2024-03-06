import * as glob from "glob";
import * as Mocha from "mocha";
import * as path from "path";

export function run(): Promise<void> {
    // Create the mocha test
    const mocha = new Mocha({
        ui: "tdd",
        color: true,
    });

    const testsRoot = path.resolve(__dirname);
    const singleFileTest: string | undefined = process.env["TEST_ARG-t"];
    const excludeFiles: string[] | undefined =
        process.env["TEST_ARG-ex"]?.split(",");
    const testPerformance: boolean =
        (process.env["TEST_ARG-test_performance"] ?? "false") === "true";

    return new Promise((c, e) => {
        glob("**/**.test.js", { cwd: testsRoot }, (err, files) => {
            if (err) {
                return e(err);
            }

            // Add files to the test suite
            files.forEach((f) => {
                if (singleFileTest) {
                    if (f.includes(singleFileTest)) {
                        mocha.addFile(path.resolve(testsRoot, f));
                    }
                } else {
                    if (f.includes("performance.test.js")) {
                        if (testPerformance) {
                            mocha.addFile(path.resolve(testsRoot, f));
                        }
                    } else if (!excludeFiles?.some((ex) => f.includes(ex))) {
                        mocha.addFile(path.resolve(testsRoot, f));
                    }
                }
            });

            try {
                // Run the mocha test
                mocha.run((failures) => {
                    if (failures > 0) {
                        e(new Error(`${failures} tests failed.`));
                    } else {
                        c();
                    }
                });
            } catch (err) {
                console.error(err);
                e(err);
            }
        });
    });
}
