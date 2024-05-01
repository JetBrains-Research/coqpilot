import * as fs from "fs";
import * as path from "path";
import * as tmp from "tmp";
import { WorkspaceConfiguration, workspace } from "vscode";

import { LLMServices, disposeServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";

import { EventLogger, Severity } from "../logging/eventLogger";

import { pluginId } from "./coqPilot";
import VSCodeLogWriter from "./vscodeLogWriter";

export class GlobalExtensionState {
    public readonly eventLogger: EventLogger = new EventLogger();
    public readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        this.parseLoggingVerbosity(workspace.getConfiguration(pluginId))
    );

    public readonly llmServicesLogsDir = path.join(
        tmp.dirSync.name,
        "llm-services-logs"
    );

    public readonly llmServices: LLMServices = {
        openAiService: new OpenAiService(
            path.join(this.llmServicesLogsDir, "openai-logs.txt"),
            this.eventLogger
        ),
        grazieService: new GrazieService(
            path.join(this.llmServicesLogsDir, "grazie-logs.txt"),
            this.eventLogger
        ),
        predefinedProofsService: new PredefinedProofsService(
            path.join(this.llmServicesLogsDir, "predefined-proofs-logs.txt"),
            this.eventLogger
        ),
        lmStudioService: new LMStudioService(
            path.join(this.llmServicesLogsDir, "lmstudio-logs.txt"),
            this.eventLogger
        ),
    };

    constructor() {}

    private parseLoggingVerbosity(config: WorkspaceConfiguration): Severity {
        const verbosity = config.get("loggingVerbosity");
        switch (verbosity) {
            case "info":
                return Severity.INFO;
            case "debug":
                return Severity.DEBUG;
            default:
                throw new Error(`Unknown logging verbosity: ${verbosity}`);
        }
    }

    dispose(): void {
        disposeServices(this.llmServices);
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
    }
}
