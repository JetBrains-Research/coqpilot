import * as fs from "fs";
import * as path from "path";
import { Disposable, WorkspaceConfiguration, window, workspace } from "vscode";

import { LLMServices, disposeServices } from "../llm/llmServices";
import { ErrorsHandlingMode } from "../llm/llmServices/commonStructures/errorsHandlingMode";
import { DeepSeekService } from "../llm/llmServices/deepSeek/deepSeekService";
import { GrazieService } from "../llm/llmServices/grazie/grazieService";
import { LLMServiceParams } from "../llm/llmServices/llmServiceParams";
import { LMStudioService } from "../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../llm/llmServices/predefinedProofs/predefinedProofsService";
import { RangoService } from "../llm/llmServices/rango/rangoService";

import { EventLogger, Severity } from "../logging/eventLogger";
import { illegalState } from "../utils/errors/throwErrors";
import { createTmpDirectory } from "../utils/fs/tmpFs";
import { ProjectRoot } from "../utils/structures/projectRoot";

import VSCodeLogWriter from "./ui/vscodeLogWriter";
import { PLUGIN_ID } from "./utils/pluginId";
import { inferProjectRoot } from "./utils/projectRootGetter";

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
    private _projectRoot: ProjectRoot | undefined = inferProjectRoot();

    getProjectRoot(): ProjectRoot | undefined {
        return this._projectRoot;
    }

    selectProjectRoot(projectRoot: ProjectRoot) {
        this._projectRoot = projectRoot;
    }

    readonly llmServicesLogsDir = path.join(
        createTmpDirectory(),
        "llm-services-logs"
    );

    private readonly llmServicesSetup: LLMServiceParams = {
        /**
         * Must be defined to provide UI with proof generation event to show to the user.
         */
        eventLogger: this.eventLogger,

        /**
         * All the necessary information about failures is obtained from the result and events;
         * so no need to abort the execution through errors, the top-level logic does not expect that
         * (even though it is protected from any errors being thrown at the user).
         */
        errorsHandlingMode: ErrorsHandlingMode.SWALLOW_ERRORS,

        /**
         * Could be turned on if debug is needed.
         */
        debugLogs: false,
    };

    readonly llmServices: LLMServices = {
        predefinedProofsService: new PredefinedProofsService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "predefined-proofs-logs.txt"
            ),
        }),
        openAiService: new OpenAiService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "openai-logs.txt"
            ),
        }),
        grazieService: new GrazieService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "grazie-logs.txt"
            ),
        }),
        lmStudioService: new LMStudioService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "lmstudio-logs.txt"
            ),
        }),
        deepSeekService: new DeepSeekService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "deepseek-logs.txt"
            ),
        }),
        rangoService: new RangoService({
            ...this.llmServicesSetup,
            generationLogsFilePath: path.join(
                this.llmServicesLogsDir,
                "rango-logs.txt"
            ),
            installationPath: undefined, // use the default one
            maxSubprocessesSpawnedInParallel: undefined, // use the default number
            clearProofGenerationLogsOnSuccess: true, // do not pollute the target directory
        }),
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
