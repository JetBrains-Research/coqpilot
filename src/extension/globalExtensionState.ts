import * as fs from "fs";
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

    // TODO: find a proper directory to store logs
    // private readonly llmServicesLogsDirName = "llm-services-logs/";
    public readonly llmServicesLogsDir = "TODO";

    public readonly llmServices: LLMServices = {
        openAiService: new OpenAiService(
            `${this.llmServicesLogsDir}openai-logs.txt`,
            this.eventLogger
        ),
        grazieService: new GrazieService(
            `${this.llmServicesLogsDir}grazie-logs.txt`,
            this.eventLogger
        ),
        predefinedProofsService: new PredefinedProofsService(
            `${this.llmServicesLogsDir}predefined-proofs-logs.txt`
        ),
        lmStudioService: new LMStudioService(
            `${this.llmServicesLogsDir}lmstudio-logs.txt`,
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
