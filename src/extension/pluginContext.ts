import * as fs from "fs";
import * as path from "path";
import * as tmp from "tmp";
import { Disposable, WorkspaceConfiguration, window, workspace } from "vscode";

import { LLMServices, disposeServices } from "../llm/llmServices";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";

import { EventLogger, Severity } from "../logging/eventLogger";

import VSCodeLogWriter from "./ui/vscodeLogWriter";
import { pluginId } from "./utils/pluginId";

export class PluginContext implements Disposable {
    public readonly eventLogger: EventLogger = new EventLogger();
    public readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        this.parseLoggingVerbosity(workspace.getConfiguration(pluginId))
    );
    public readonly logOutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    );

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
        disposeServices(this.llmServices);
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
        this.logOutputChannel.dispose();
    }
}
