import { Configuration } from "@tsed/common";
import { Env } from "@tsed/core";
import "@tsed/platform-express";
import "@tsed/swagger";

import { CoqProjectController } from "./controllers/coqProjectController";
import { GlobalErrorHandlerMiddleware } from "./middlewares/globalErrorHandlerMiddleware";

const rootDir = __dirname;

// eslint-disable-next-line prettier/prettier
@Configuration({
    rootDir,
    acceptMimes: ["application/json"],
    httpPort: process.env.PORT || 8000,
    httpsPort: false,
    logger: {
        debug: true,
        logRequest: true,
        requestFields: ["method", "url", "headers", "query", "params"],
    },
    mount: {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "/rest": [CoqProjectController],
    },
    middlewares: [
        "cors",
        "json-parser",
        "compression",
        "method-override",
        GlobalErrorHandlerMiddleware,
    ],
    swagger: [
        {
            path: "/docs",
            cssPath: `${rootDir}/../../src/agentServer/spec/style.css`,
        },
    ],
    env: Env.DEV,
})
export class Server {}
