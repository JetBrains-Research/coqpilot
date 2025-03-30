import * as fs from "fs";
import * as path from "path";
import * as tmp from "tmp";
import { Disposable, WorkspaceConfiguration, window, workspace } from "vscode";

import { LLMServices, disposeServices } from "../llm/llmServices";
import { ErrorsHandlingMode } from "../llm/llmServices/commonStructures/errorsHandlingMode";
import { DeepSeekService } from "../llm/llmServices/deepSeek/deepSeekService";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import { RangoService } from "../llm/llmServices/rango/rangoService";

import { EventLogger, Severity } from "../logging/eventLogger";
import { illegalState } from "../utils/errors/throwErrors";
import { Uri } from "../utils/structures/uri";

import VSCodeLogWriter from "./ui/vscodeLogWriter";
import { PLUGIN_ID } from "./utils/pluginId";
import { getOpenedWorkspaceAsProjectRoot } from "./utils/projectRootGetter";

export class PluginContext implements Disposable {
    readonly eventLogger: EventLogger = new EventLogger();
    readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        this.parseLoggingVerbosity(workspace.getConfiguration(PLUGIN_ID))
    );
    readonly logOutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    );

    // TODO: support a way in the UI to reconfigure it manually
    private _projectRootUri: Uri | undefined =
        getOpenedWorkspaceAsProjectRoot();

    getProjectRoot(): Uri | undefined {
        return this._projectRootUri;
    }

    selectProjectRoot(projectRoot: Uri) {
        this._projectRootUri = projectRoot;
    }

    readonly llmServicesLogsDir = path.join(
        tmp.dirSync().name,
        "llm-services-logs"
    );

    private readonly llmServicesSetup = {
        // must be defined to provide UI with proof generation event to show to the user
        eventLogger: this.eventLogger,
        // all the necessary information about failures is obtained from the result and events;
        // so no need to abort the execution through errors, the top-level logic does not expect that
        // (even though protects from any errors being thrown at the user)
        errorsHandlingMode: ErrorsHandlingMode.SWALLOW_ERRORS,
        // could be turned on if debug is needed
        debugLogs: false,
    };

    readonly llmServices: LLMServices = {
        predefinedProofsService: new PredefinedProofsService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "predefined-proofs-logs.txt"),
            this.llmServicesSetup.debugLogs
        ),
        openAiService: new OpenAiService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "openai-logs.txt"),
            this.llmServicesSetup.debugLogs
        ),
        grazieService: new GrazieService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "grazie-logs.txt"),
            this.llmServicesSetup.debugLogs
        ),
        lmStudioService: new LMStudioService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "lmstudio-logs.txt"),
            this.llmServicesSetup.debugLogs
        ),
        deepSeekService: new DeepSeekService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "deepseek-logs.txt"),
            this.llmServicesSetup.debugLogs
        ),
        rangoService: new RangoService(
            this.llmServicesSetup.eventLogger,
            this.llmServicesSetup.errorsHandlingMode,
            path.join(this.llmServicesLogsDir, "rango-logs.txt"),
            this.llmServicesSetup.debugLogs,
            undefined // use the default path to Rango
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
                illegalState(`unknown logging verbosity: ${verbosity}`);
        }
    }

    dispose(): void {
        disposeServices(this.llmServices);
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
        this.logOutputChannel.dispose();
    }
}
