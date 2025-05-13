import * as fs from "fs";
import * as path from "path";
import { Disposable, WorkspaceConfiguration, window, workspace } from "vscode";

import { ErrorsHandlingMode } from "../llm/llmServices/commonStructures/errorsHandlingMode";
import {
    CorrespondingInputServiceParams,
    LLMServiceIdentifier,
} from "../llm/llmServices/llmServiceIdentifier";
import { LLMServiceParams } from "../llm/llmServices/llmServiceParams";
import { selectLLMServiceProvider } from "../llm/llmServices/llmServiceProvider";
import {
    BasicLLMServiceCustomizationParams,
    LLMServiceControlParams,
} from "../llm/llmServices/utils/llmServiceControlParams";
import { getShortName } from "../llm/llmServices/utils/serialization/toLog";
import { LLMServicesStorage } from "../llm/llmServicesStorage";

import { EventLogger, Severity } from "../logging/eventLogger";
import { illegalState } from "../utils/errors/throwErrors";
import {
    addExtension,
    translateToSafeFileName,
} from "../utils/fs/fileNameUtils";
import { createTmpDirectory } from "../utils/fs/tmpFs";
import { ProjectRoot } from "../utils/structures/projectRoot";

import VSCodeLogWriter from "./ui/vscodeLogWriter";
import { PLUGIN_ID } from "./utils/pluginId";
import { inferProjectRoot } from "./utils/projectRootGetter";

type ServiceEntry<T extends LLMServiceIdentifier> = [
    T,
    CorrespondingInputServiceParams<T>,
];

function serviceEntry<T extends LLMServiceIdentifier>(
    serviceId: T,
    customParams: CorrespondingInputServiceParams<T> = {} as any
): ServiceEntry<T> {
    return [serviceId, customParams];
}

export class PluginContext implements Disposable {
    readonly eventLogger: EventLogger = new EventLogger();
    readonly logWriter: VSCodeLogWriter = new VSCodeLogWriter(
        this.eventLogger,
        PluginContext.parseLoggingVerbosity(
            workspace.getConfiguration(PLUGIN_ID)
        )
    );
    readonly logOutputChannel = window.createOutputChannel(
        "CoqPilot: coq-lsp events"
    );

    readonly llmServicesLogsDir = path.join(
        createTmpDirectory(),
        "llm-services-logs"
    );

    private readonly llmServicesControlParams: LLMServiceControlParams = {
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
    };

    readonly llmServices: LLMServicesStorage = PluginContext.registerServices(
        this.llmServicesLogsDir,
        this.llmServicesControlParams
    );

    // TODO: support a way in the UI to reconfigure it manually
    private _projectRoot: ProjectRoot | undefined = inferProjectRoot();

    getProjectRoot(): ProjectRoot | undefined {
        return this._projectRoot;
    }

    selectProjectRoot(projectRoot: ProjectRoot) {
        this._projectRoot = projectRoot;
    }

    dispose(): void {
        this.llmServices.dispose();
        this.logWriter.dispose();
        fs.rmSync(this.llmServicesLogsDir, { recursive: true, force: true });
        this.logOutputChannel.dispose();
    }

    private static readonly llmServicesCustomizationParams: BasicLLMServiceCustomizationParams =
        {
            /**
             * Use the safest option by default: this way,
             * the overall progress is guaranteed
             * (although potentially slowing down the whole process).
             */
            generationParallelism: 1,

            /**
             * Could be turned on if debug is needed.
             */
            debugLogs: false,
        };

    private static readonly servicesToRegister = [
        serviceEntry(LLMServiceIdentifier.PREDEFINED_PROOFS),
        serviceEntry(LLMServiceIdentifier.OPENAI, {
            generationParallelism: 5, // In practice, `OpenAI` is capable of processing multiple requests.
        }),
        serviceEntry(LLMServiceIdentifier.GRAZIE),
        serviceEntry(LLMServiceIdentifier.LMSTUDIO),
        serviceEntry(LLMServiceIdentifier.DEEPSEEK),
        serviceEntry(LLMServiceIdentifier.RANGO, {
            installationPath: undefined, // use the default one
            maxSubprocessesSpawnedInParallel: undefined, // use the default number
            clearProofGenerationLogsOnSuccess: true, // do not pollute the target directory
        }),
    ];

    private static registerServices(
        llmServicesLogsDir: string,
        llmServicesControlParams: LLMServiceControlParams
    ): LLMServicesStorage {
        const llmServices = new LLMServicesStorage();
        try {
            for (const [serviceId, customParams] of this.servicesToRegister) {
                const serviceParams: LLMServiceParams = {
                    ...this.llmServicesCustomizationParams,
                    generationLogsFilePath: path.join(
                        llmServicesLogsDir,
                        addExtension(
                            translateToSafeFileName(
                                `${getShortName(serviceId)}-logs`
                            ),
                            ".txt"
                        )
                    ),
                    ...customParams,
                };
                llmServices.registerService(() =>
                    selectLLMServiceProvider(
                        serviceId,
                        serviceParams
                    )(llmServicesControlParams)
                );
            }
            return llmServices;
        } catch (e) {
            llmServices.dispose();
            throw e;
        }
    }

    private static parseLoggingVerbosity(
        config: WorkspaceConfiguration
    ): Severity {
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
}
