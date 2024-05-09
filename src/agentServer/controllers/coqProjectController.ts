import {Controller, Get} from "@tsed/common";

// eslint-disable-next-line prettier/prettier
@Controller("/document")
export class CoqProjectController {
    @Get()
    getProjectRoot(): any {
        return {
            message: "Server is expecting the coq project to be with the same root as the server.",
            projectRoot: process.cwd(),
        };
    }
}
