import {Controller, Get, PathParams} from "@tsed/common";
import {CoqProjectObserverService} from "../services/coqProjectObserverService";

// eslint-disable-next-line prettier/prettier
@Controller("/document")
export class CoqProjectController {
    constructor(private coqProjectObserverService: CoqProjectObserverService) {}

    @Get()
    getProjectRoot(): any {
        return {
            message: "Server is expecting the coq project to be with the same root as the server.",
            projectRoot: this.coqProjectObserverService.getProjectRoot(),
        };
    }

    @Get("/theoremNames/:filePath")
    async getTheoremNamesFromFile(@PathParams("filePath") filePath: string): Promise<any> {
        return {
            message: "Theorem names from the file",
            theoremNames: await this.coqProjectObserverService.getTheoremNamesFromFile(filePath),
        };
    }

}
