import { Middleware, QueryParams } from "@tsed/common";
import { BadRequest, InternalServerError } from "@tsed/exceptions";
import { existsSync } from "fs";

// eslint-disable-next-line prettier/prettier
@Middleware()
export class FilePathMiddleware {
    async use(@QueryParams("filePath") filePath: string) {
        const projectRoot = process.env.SERVER_RUN_ROOT;
        if (!projectRoot) {
            throw new InternalServerError("Unable to find the project root");
        }

        const absFilePath = `${projectRoot}/${filePath}`;
        if (!existsSync(absFilePath)) {
            throw new BadRequest("The file does not exist");
        }   
    }
}