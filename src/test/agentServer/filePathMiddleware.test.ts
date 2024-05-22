import { expect } from "earl";

import { FilePathMiddleware } from "../../agentServer/middlewares/filePathMiddleware";

import { serverRunRoot } from "./commonServerTestFunctions";

process.env.SERVER_RUN_ROOT = serverRunRoot;

suite("[AgentServer] FilePath Middleware tests", () => {
    test("Valid file path", async () => {
        const middleware = new FilePathMiddleware();
        expect(await middleware.use("small_document.v")).toBeNullish();
    });

    test("Invalid file path", async () => {
        const middleware = new FilePathMiddleware();
        await expect(middleware.use("file.txt")).toBeRejectedWith(
            "The file is not a Coq file"
        );
    });

    test("Nonexistent file", async () => {
        const middleware = new FilePathMiddleware();
        await expect(middleware.use("nonexistent.v")).toBeRejectedWith(
            "The file does not exist"
        );
    });
});
