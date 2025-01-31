import { withTestCoqLspClient } from "../../../../../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../../../../../coqLsp/coqLspClient";
import { CoqLspError } from "../../../../../coqLsp/coqLspTypes";

import { createSourceFileEnvironment } from "../../../../../core/inspectSourceFile";

import { unexpectedError } from "../../../../../utils/throwErrors";
import { Uri } from "../../../../../utils/uri";
import { BenchmarkingLogger } from "../../../logging/benchmarkingLogger";
import { TargetType } from "../../../structures/benchmarkingCore/completionGenerationTask";
import { deserializeCodeElementPosition } from "../../../structures/common/codeElementPositions";
import { TargetRequestType } from "../../../structures/common/inputTargets";
import { SerializedParsedCoqFile } from "../../../structures/parsedCoqFile/parsedCoqFileData";
import {
    SerializedProofStep,
    SerializedTheorem,
    TheoremData,
    serializeTheoremData,
} from "../../../structures/parsedCoqFile/theoremData";
import { FailFastAbortError } from "../../../utils/asyncUtils/abortUtils";
import {
    mappedObjectValues,
    packIntoMappedObject,
} from "../../../utils/collectionUtils/mapUtils";
import {
    SerializedGoal,
    serializeGoal,
} from "../../../utils/coqUtils/goalParser";
import { extractSerializedTheoremFisrtProofStep } from "../../../utils/coqUtils/proofTargetExtractor";
import { LogsIPCSender } from "../../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { throwBenchmarkingError } from "../../../utils/throwErrors";

import { ParseCoqProjectInternalSignature } from "./internalSignature";

/**
 * **Warning:** This implementation requires the `vscode` module to function.
 * It should not be used in code executed outside the `test-electron` environment.
 */
export namespace ParseCoqProjectImpl {
    import Signature = ParseCoqProjectInternalSignature;

    export type Logger = LogsIPCSender | BenchmarkingLogger;

    export async function parseCoqProject(
        args: Signature.ArgsModels.Args,
        logger: Logger
    ): Promise<Signature.ResultModels.Result> {
        const parsedWorkspace: Signature.ResultModels.Result = {};

        // Note: specific abort controller is not passed here, since
        // the abort behaviour is not supported (and not needed) at the parsing stage.
        await withTestCoqLspClient(
            { workspaceRootPath: args.workspaceRootPath },
            async (coqLspClient) => {
                for (const filePath in args.workspaceTargets) {
                    parsedWorkspace[filePath] =
                        await coqLspClient.withTextDocument(
                            {
                                uri: Uri.fromPath(filePath),
                                timeoutMillis: args.openDocumentTimeoutMillis,
                            },
                            () =>
                                parseFileTargets(
                                    args.workspaceTargets[filePath],
                                    filePath,
                                    coqLspClient,
                                    logger
                                )
                        );
                }
            }
        );

        logger.debug(
            `Successfully parsed Coq project: analyzed ${Object.keys(parsedWorkspace).length} files`
        );
        return parsedWorkspace;
    }

    async function parseFileTargets(
        fileTargets: Signature.ArgsModels.FileTarget[],
        filePath: string,
        coqLspClient: CoqLspClient,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileResults> {
        const serializedParsedFile = await parseSourceFile(
            filePath,
            coqLspClient,
            logger
        );
        return {
            serializedParsedFile: serializedParsedFile,
            parsedFileTargets: await extractFileTargetsFromFile(
                fileTargets,
                serializedParsedFile,
                coqLspClient,
                logger
            ),
        };
    }

    async function parseSourceFile(
        filePath: string,
        coqLspClient: CoqLspClient,
        logger: Logger
    ): Promise<SerializedParsedCoqFile> {
        const mockDocumentVersion = 1;
        const sourceFileEnvironment = await createSourceFileEnvironment(
            mockDocumentVersion,
            Uri.fromPath(filePath),
            coqLspClient,
            new AbortController().signal, // abort behaviour is not supported at the parsing stage
            true // TODO: pass `ContextTheoremsRanker.needsUnwrappedNotations` here to improve performance
        );
        const serializedParsedFile: SerializedParsedCoqFile = {
            serializedTheoremsByNames: packIntoMappedObject(
                sourceFileEnvironment.fileTheorems.map(
                    (theorem, fileTheoremsIndex) =>
                        serializeTheoremData(
                            new TheoremData(theorem, fileTheoremsIndex)
                        )
                ),
                (serializedTheorem) => serializedTheorem.name,
                (serializedTheorem) => serializedTheorem
            ),
            documentVersion: sourceFileEnvironment.documentVersion,
            filePath: filePath,
        };
        const foundTheoremsLog = `found ${Object.keys(serializedParsedFile.serializedTheoremsByNames).length} theorem(s)`;
        logger.debug(`Successfully parsed "${filePath}": ${foundTheoremsLog}`);
        return serializedParsedFile;
    }

    async function extractFileTargetsFromFile(
        fileTargets: Signature.ArgsModels.FileTarget[],
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClient,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileTarget[]> {
        const parsedTargetsSets: Signature.ResultModels.ParsedFileTarget[][] =
            [];
        const theoremsMapping = serializedParsedFile.serializedTheoremsByNames;

        for (const fileTarget of fileTargets) {
            if (fileTarget.specificTheoremName === undefined) {
                // all theorems requests
                for (const serializedTheorem of mappedObjectValues(
                    theoremsMapping
                )) {
                    const parsedTargetsFromTheorem =
                        await extractTargetsFromTheorem(
                            serializedTheorem,
                            fileTarget.requestType,
                            serializedParsedFile,
                            coqLspClient,
                            logger
                        );
                    parsedTargetsSets.push(parsedTargetsFromTheorem);
                }
            } else {
                // specific theorems requests
                const theoremName = fileTarget.specificTheoremName;
                if (!(theoremName in theoremsMapping)) {
                    throwBenchmarkingError(
                        `Requested theorem "${theoremName}" could not be found `,
                        `in ${serializedParsedFile.filePath} file`
                    );
                }
                const parsedTargetsFromTheorem =
                    await extractTargetsFromTheorem(
                        theoremsMapping[theoremName],
                        fileTarget.requestType,
                        serializedParsedFile,
                        coqLspClient,
                        logger
                    );
                parsedTargetsSets.push(parsedTargetsFromTheorem);
            }
        }

        return parsedTargetsSets.flat();
    }

    async function extractTargetsFromTheorem(
        serializedTheorem: SerializedTheorem,
        requestType: TargetRequestType,
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClient,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileTarget[]> {
        const targetBuilder: (
            proofStep: SerializedProofStep,
            targetType: TargetType,
            knownGoal: SerializedGoal | undefined
        ) => Promise<Signature.ResultModels.ParsedFileTarget> = async (
            proofStep,
            targetType,
            knownGoal
        ) => {
            return {
                theoremName: serializedTheorem.name,
                targetType: targetType,
                goalToProve:
                    knownGoal ??
                    (await parseGoal(
                        proofStep,
                        serializedParsedFile,
                        coqLspClient,
                        logger
                    )),
                positionRange: proofStep.range,
            };
        };
        switch (requestType) {
            case TargetRequestType.THEOREM_PROOF:
                const theoremProofTarget = await targetBuilder(
                    extractSerializedTheoremFisrtProofStep(serializedTheorem),
                    TargetType.PROVE_THEOREM,
                    serializedTheorem.initial_goal
                );
                if (serializedTheorem.initial_goal === undefined) {
                    serializedTheorem.initial_goal =
                        theoremProofTarget.goalToProve;
                }
                return [theoremProofTarget];
            case TargetRequestType.ALL_ADMITS:
                const parsedTargets = [];
                for (const holeProofStep of serializedTheorem.proof!.holes) {
                    parsedTargets.push(
                        await targetBuilder(
                            holeProofStep,
                            TargetType.ADMIT,
                            undefined
                        )
                    );
                }
                return parsedTargets;
        }
    }

    async function parseGoal(
        proofStep: SerializedProofStep,
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClient,
        logger: Logger
    ): Promise<SerializedGoal> {
        const startPosition = deserializeCodeElementPosition(
            proofStep.range.start
        );
        try {
            const goal = await coqLspClient.getFirstGoalAtPointOrThrow(
                proofStep.range.start,
                Uri.fromPath(serializedParsedFile.filePath),
                serializedParsedFile.documentVersion
            );
            logger.debug(
                `Successfully retrieved target goal at point: "${goal.ty}" at ${startPosition}, "${serializedParsedFile.filePath}"`
            );
            return serializeGoal(goal);
        } catch (err) {
            if (err instanceof CoqLspError) {
                const stack = err.stack === undefined ? "" : `\n${err.stack}`;
                logger.error(
                    `Failed to retrieve target goal at point: "${err.message}" at ${startPosition}, "${serializedParsedFile.filePath}"${stack}`
                );
                throw err;
            } else if (err instanceof FailFastAbortError) {
                throw err;
            }
            unexpectedError(err);
        }
    }
}
