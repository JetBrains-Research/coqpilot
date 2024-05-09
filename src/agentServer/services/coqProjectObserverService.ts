import { Injectable } from "@tsed/di";
import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";
import { Uri } from "../../utils/uri";
import { parseCoqFile } from "../../coqParser/parseCoqFile";

export class ServerError extends Error {
    constructor(message: string) {
        super(message);
        this.name = "ServerError";
    }
}


// eslint-disable-next-line prettier/prettier
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
        this.coqLspClient = new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
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
}