import {Configuration} from "@tsed/common";
import "@tsed/platform-express";
import "@tsed/swagger";
import {CoqProjectController} from "./controllers/coqProjectController";

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
        requestFields: ["method", "url", "headers", "query", "params"]
    },
    mount: {
        // eslint-disable-next-line @typescript-eslint/naming-convention
        "/rest": [
            CoqProjectController
        ]
    },
    middlewares: [
        "cors",
        "json-parser",
        "compression",
        "method-override",
    ],
    swagger: [
        {
            path: "/docs",
            cssPath: `${rootDir}/spec/style.css`,
        }
    ],
})
export class Server {}
