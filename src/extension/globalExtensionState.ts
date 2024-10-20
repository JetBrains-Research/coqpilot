import * as fs from "fs";
import * as path from "path";
import * as tmp from "tmp";
import {
    OutputChannel,
    WorkspaceConfiguration,
    window,
    workspace,
} from "vscode";

import { LLMServices, disposeServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";

import { createCoqLspClient } from "../coqLsp/coqLspBuilders";
import { CoqLspClientInterface } from "../coqLsp/coqLspClient";

import { EventLogger, Severity } from "../logging/eventLogger";

import { parseCoqLspServerPath } from "./configReaders";
import { pluginId } from "./coqPilot";
import VSCodeLogWriter from "./vscodeLogWriter";

export class GlobalExtensionState {
    public readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        this.parseLoggingVerbosity(workspace.getConfiguration(pluginId))
    );

    private constructor(
        public readonly coqLspClient: CoqLspClientInterface,
        public readonly logOutputChannel: OutputChannel,
        public readonly eventLogger: EventLogger
    ) {}

    static async create(): Promise<GlobalExtensionState> {
        const coqLspServerPath = parseCoqLspServerPath();
        const logOutputChannel = window.createOutputChannel(
            "CoqPilot: coq-lsp events"
        );
        const eventLogger = new EventLogger();
        const coqLspClient = await createCoqLspClient(
            coqLspServerPath,
            logOutputChannel,
            eventLogger
        );

        return new GlobalExtensionState(
            coqLspClient,
            logOutputChannel,
            eventLogger
        );
    }

    public readonly llmServicesLogsDir = path.join(
        tmp.dirSync().name,
        "llm-services-logs"
    );

    public readonly llmServices: LLMServices = {
        predefinedProofsService: new PredefinedProofsService(
            this.eventLogger,
            false,
            path.join(this.llmServicesLogsDir, "predefined-proofs-logs.txt")
        ),
        openAiService: new OpenAiService(
            this.eventLogger,
            false,
            path.join(this.llmServicesLogsDir, "openai-logs.txt")
        ),
        grazieService: new GrazieService(
            this.eventLogger,
            false,
            path.join(this.llmServicesLogsDir, "grazie-logs.txt")
        ),
        lmStudioService: new LMStudioService(
            this.eventLogger,
            false,
            path.join(this.llmServicesLogsDir, "lmstudio-logs.txt")
        ),
    };

    private parseLoggingVerbosity(config: WorkspaceConfiguration): Severity {
        const verbosity = config.get("loggingVerbosity");
        switch (verbosity) {
            case "info":
                return Severity.INFO;
            case "debug":
                return Severity.DEBUG;
            default:
                throw Error(`unknown logging verbosity: ${verbosity}`);
        }
    }

    dispose(): void {
        this.coqLspClient.dispose();
        disposeServices(this.llmServices);
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
        this.logOutputChannel.dispose();
    }
}
