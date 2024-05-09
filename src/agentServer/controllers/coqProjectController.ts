import { Controller, Get, QueryParams, UseBefore } from "@tsed/common";

import { FilePathMiddleware } from "../middlewares/filePathMiddleware";
import { CoqProjectObserverService } from "../services/coqProjectObserverService";

@Controller("/document")
export class CoqProjectController {
    constructor(private coqProjectObserverService: CoqProjectObserverService) {}

    @Get()
    getProjectRoot(): any {
        return {
            message:
                "Server is expecting the coq project to be with the same root as the server.",
            projectRoot: this.coqProjectObserverService.getProjectRoot(),
        };
    }

    @Get("/theorem-names")
    @UseBefore(FilePathMiddleware)
    async getTheoremNamesFromFile(
        @QueryParams("filePath") filePath: string
    ): Promise<any> {
        return {
            message: "Theorem names from the file",
            theoremNames:
                await this.coqProjectObserverService.getTheoremNamesFromFile(
                    filePath
                ),
        };
    }

    @Get("/all-coq-files")
    getAllCoqFiles(): any {
        return {
            coqFiles: this.coqProjectObserverService.getCoqFilesInProject(),
        };
    }

    @Get("/theorem")
    @UseBefore(FilePathMiddleware)
    async retrieveTheoremFromFile(
        @QueryParams("filePath") filePath: string,
        @QueryParams("theoremName") theoremName: string
    ): Promise<any> {
        const theorem =
            await this.coqProjectObserverService.retrieveTheoremFromFile(
                filePath,
                theoremName
            );
        return {
            theoremStatement: theorem.statement,
            theoremProof: theorem.proof?.onlyText() || "Admitted.",
        };
    }
}
