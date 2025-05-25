import * as fs from "fs";
import * as path from "path";
import { Disposable, WorkspaceConfiguration, window, workspace } from "vscode";

import { ErrorsHandlingMode } from "../proofProviders/impl/commonStructures/errorsHandlingMode";
import { selectProofProviderConstructor } from "../proofProviders/impl/proofProviderConstructor";
import {
    CorrespondingInputProofProviderParams,
    ProofProviderIdentifier,
} from "../proofProviders/impl/proofProviderIdentifier";
import { getShortName } from "../proofProviders/impl/proofProviderIdentifier";
import { ProofProviderParams } from "../proofProviders/impl/proofProviderParams";
import {
    BasicProofProviderCustomizationParams,
    ProofProviderControlParams,
} from "../proofProviders/impl/utils/proofProviderControlParams";
import { ProofProvidersStorage } from "../proofProviders/proofProvidersStorage";

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

type ProofProviderEntry<T extends ProofProviderIdentifier> = [
    T,
    CorrespondingInputProofProviderParams<T>,
];

function proofProviderEntry<T extends ProofProviderIdentifier>(
    proofProviderId: T,
    customParams: CorrespondingInputProofProviderParams<T> = {} as any
): ProofProviderEntry<T> {
    return [proofProviderId, customParams];
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

    readonly proofProvidersLogsDir = path.join(
        createTmpDirectory(),
        "proof-providers-logs"
    );

    private readonly proofProvidersControlParams: ProofProviderControlParams = {
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

    readonly proofProviders: ProofProvidersStorage =
        PluginContext.registerProofProviders(
            this.proofProvidersLogsDir,
            this.proofProvidersControlParams
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
        this.proofProviders.dispose();
        this.logWriter.dispose();
        fs.rmSync(this.proofProvidersLogsDir, { recursive: true, force: true });
        this.logOutputChannel.dispose();
    }

    private static readonly proofProvidersCustomizationParams: BasicProofProviderCustomizationParams =
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

    private static readonly proofProvidersToRegister = [
        proofProviderEntry(ProofProviderIdentifier.PREDEFINED_PROOFS),
        proofProviderEntry(ProofProviderIdentifier.OPENAI, {
            generationParallelism: 5, // In practice, `OpenAI` is capable of processing multiple requests.
        }),
        proofProviderEntry(ProofProviderIdentifier.GRAZIE),
        proofProviderEntry(ProofProviderIdentifier.LMSTUDIO),
        proofProviderEntry(ProofProviderIdentifier.DEEPSEEK),
        proofProviderEntry(ProofProviderIdentifier.RANGO, {
            installationPath: undefined, // use the default one
            maxSubprocessesSpawnedInParallel: undefined, // use the default number
            clearProofGenerationLogsOnSuccess: true, // do not pollute the target directory
        }),
    ];

    private static registerProofProviders(
        proofProvidersLogsDir: string,
        proofProvidersControlParams: ProofProviderControlParams
    ): ProofProvidersStorage {
        const proofProviders = new ProofProvidersStorage();
        try {
            for (const [proofProviderId, customParams] of this
                .proofProvidersToRegister) {
                const proofProviderParams: ProofProviderParams = {
                    ...this.proofProvidersCustomizationParams,
                    generationLogsFilePath: path.join(
                        proofProvidersLogsDir,
                        addExtension(
                            translateToSafeFileName(
                                `${getShortName(proofProviderId)}-logs`
                            ),
                            ".txt"
                        )
                    ),
                    ...customParams,
                };
                proofProviders.registerProofProvider(() =>
                    selectProofProviderConstructor(
                        proofProviderId,
                        proofProviderParams
                    )(proofProvidersControlParams)
                );
            }
            return proofProviders;
        } catch (e) {
            proofProviders.dispose();
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
