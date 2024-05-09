import { Injectable } from "@tsed/di";
import { BadRequest } from "@tsed/exceptions";
import { lstatSync, readdirSync } from "fs";
import * as path from "path";

import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";

import { parseCoqFile } from "../../coqParser/parseCoqFile";
import { Theorem } from "../../coqParser/parsedTypes";
import { Uri } from "../../utils/uri";
import { CoqFile } from "../models/coqFile";

@Injectable()
export class CoqProjectObserverService {
    private readonly projectRoot: string;
    private readonly coqLspClient: CoqLspClient;

    constructor() {
        const projectRoot = process.env.SERVER_RUN_ROOT;
        if (!projectRoot) {
            throw new Error("Unable to find the project root");
        }

        this.projectRoot = projectRoot;
        const coqLspServerConfig = CoqLspConfig.createServerConfig();
        const coqLspClientConfig = CoqLspConfig.createClientConfig(
            process.env.COQ_LSP_PATH || "coq-lsp",
            this.projectRoot
        );
        this.coqLspClient = new CoqLspClient(
            coqLspServerConfig,
            coqLspClientConfig
        );
    }

    getProjectRoot(): string {
        return this.projectRoot;
    }

    /**
     * Accepts relative path inside the project
     * Closes the document after parsing
     */
    async getTheoremNamesFromFile(filePath: string): Promise<string[]> {
        const absolutePath = `${this.projectRoot}/${filePath}`;
        const fileUri = Uri.fromPath(absolutePath);
        await this.coqLspClient.openTextDocument(fileUri);
        const document = await parseCoqFile(fileUri, this.coqLspClient);
        await this.coqLspClient.closeTextDocument(fileUri);

        return document.map((theorem) => theorem.name);
    }

    async retrieveTheoremFromFile(
        filePath: string,
        theoremName: string
    ): Promise<Theorem> {
        const absolutePath = `${this.projectRoot}/${filePath}`;
        const fileUri = Uri.fromPath(absolutePath);
        await this.coqLspClient.openTextDocument(fileUri);
        const document = await parseCoqFile(fileUri, this.coqLspClient);
        await this.coqLspClient.closeTextDocument(fileUri);

        const theorem = document.find(
            (theorem) => theorem.name === theoremName
        );
        if (!theorem) {
            throw new BadRequest(
                `Theorem ${theoremName} not found in file ${filePath}`
            );
        }

        return theorem;
    }

    getCoqFilesInProject(): CoqFile[] {
        let coqFiles: CoqFile[] = [];

        function finder(startPath: string, rootPath: string): void {
            let files: string[] = readdirSync(startPath);

            for (let file of files) {
                let filename = path.join(startPath, file);
                let stats = lstatSync(filename);

                if (stats.isDirectory()) {
                    finder(filename, rootPath);
                } else if (filename.slice(-2) === ".v") {
                    coqFiles.push({
                        name: file,
                        pathFromRoot: path.relative(rootPath, filename),
                    });
                }
            }
        }

        finder(this.projectRoot, this.projectRoot);
        return coqFiles;
    }
}
