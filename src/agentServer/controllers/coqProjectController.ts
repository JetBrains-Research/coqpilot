import { Controller, Get, QueryParams, UseBefore } from "@tsed/common";
import { Required } from "@tsed/schema";

import { FilePathMiddleware } from "../middlewares/filePathMiddleware";
import { CoqProjectObserverService } from "../services/coqProjectObserverService";

// eslint-disable-next-line prettier/prettier
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
        @Required() @QueryParams("filePath") filePath: string
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
        @Required() @QueryParams("filePath") filePath: string,
        @Required() @QueryParams("theoremName") theoremName: string
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

    @Get("/run-command")
    @UseBefore(FilePathMiddleware)
    async runCommandInFile(
        @Required() @QueryParams("filePath") filePath: string,
        @Required() @QueryParams("command") coqCommand: string
    ): Promise<any> {
        const execResult =
            await this.coqProjectObserverService.runCoqCommand(
                filePath,
                coqCommand
            );
        return {
            command: coqCommand,
            result: execResult,
        };
    }

    @Get("/check-proof")
    @UseBefore(FilePathMiddleware)
    async checkProofInFile(
        @Required() @QueryParams("filePath") filePath: string,
        @Required() @QueryParams("theoremWithProof") coqCommand: string
    ): Promise<any> {
        const execResult =
            await this.coqProjectObserverService.checkCoqProof(
                filePath,
                coqCommand
            );
        return {
            command: coqCommand,
            result: execResult === undefined ? "Proof is complete. No goals left." : execResult,
        };
    }
}
