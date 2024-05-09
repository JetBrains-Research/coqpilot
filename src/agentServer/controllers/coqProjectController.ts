import {Controller, Get} from "@tsed/common";

// eslint-disable-next-line prettier/prettier
@Controller("/document")
export class CoqProjectController {
    @Get()
    findAll(): any {
        return {
            id: "1",
            name: "Project 1",
        };
    }
}
