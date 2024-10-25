import { createTestCoqLspClient } from "../../../../../coqLsp/coqLspBuilders";
import { CoqLspClientInterface } from "../../../../../coqLsp/coqLspClient";

import { createSourceFileEnvironment } from "../../../../../core/inspectSourceFile";

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
import {
    mappedObjectValues,
    packIntoMappedObject,
} from "../../../utils/collectionUtils/mapUtils";
import {
    SerializedGoal,
    serializeGoal,
} from "../../../utils/coqUtils/goalParser";
import { LogsIPCSender } from "../../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";

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
        const coqLspClient = await createTestCoqLspClient(
            args.workspaceRootPath
        );
        const parsedWorkspace: Signature.ResultModels.Result = {};
        for (const filePath in args.workspaceTargets) {
            const fileTargets = args.workspaceTargets[filePath];
            const serializedParsedFile = await openAndParseSourceFile(
                filePath,
                coqLspClient,
                logger
            );
            const parsedFileResults: Signature.ResultModels.ParsedFileResults =
                {
                    serializedParsedFile: serializedParsedFile,
                    parsedFileTargets: await extractFileTargetsFromFile(
                        fileTargets,
                        serializedParsedFile,
                        coqLspClient,
                        logger
                    ),
                };
            parsedWorkspace[filePath] = parsedFileResults;
        }
        logger.debug(
            `Successfully parsed Coq project: analyzed ${Object.keys(parsedWorkspace).length} files`
        );
        return parsedWorkspace;
    }

    async function openAndParseSourceFile(
        filePath: string,
        coqLspClient: CoqLspClientInterface,
        logger: Logger
    ): Promise<SerializedParsedCoqFile> {
        const mockFileVersion = 1;
        const sourceFileUri = Uri.fromPath(filePath);
        await coqLspClient.openTextDocument(sourceFileUri);
        const abortController = new AbortController();
        const sourceFileEnvironment = await createSourceFileEnvironment(
            mockFileVersion,
            sourceFileUri,
            coqLspClient,
            abortController.signal
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
            fileLines: sourceFileEnvironment.fileLines,
            fileVersion: sourceFileEnvironment.fileVersion,
            filePath: filePath,
        };
        const foundTheoremsLog = `found ${Object.keys(serializedParsedFile.serializedTheoremsByNames).length} theorem(s)`;
        const readLinesLog = `read ${serializedParsedFile.fileLines.length} lines`;
        logger.debug(
            `Successfully parsed "${filePath}": ${foundTheoremsLog}, ${readLinesLog}`
        );
        return serializedParsedFile;
    }

    async function extractFileTargetsFromFile(
        fileTargets: Signature.ArgsModels.FileTarget[],
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClientInterface,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileTarget[]> {
        const parsedTargetsSets: Signature.ResultModels.ParsedFileTarget[][] =
            [];
        const theoremsMapping = serializedParsedFile.serializedTheoremsByNames;

        for (const fileTarget of fileTargets) {
            if (fileTarget.specificTheoremName === undefined) {
                // all theorems requests
                for (const theorem of mappedObjectValues(theoremsMapping)) {
                    const parsedTargetsFromTheorem =
                        await extractTargetsFromTheorem(
                            theorem,
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
                    throw Error(
                        `Requested theorem "${theoremName}" could not be found in ${serializedParsedFile.filePath} file`
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
        theorem: SerializedTheorem,
        requestType: TargetRequestType,
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClientInterface,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileTarget[]> {
        const targetBuilder: (
            proofStep: SerializedProofStep,
            targetType: TargetType,
            knownGoal: SerializedGoal | undefined
        ) => Promise<Signature.ResultModels.ParsedFileTarget> = (
            proofStep,
            targetType,
            knownGoal
        ) =>
            buildParsedFileTarget(
                proofStep,
                targetType,
                theorem.name,
                knownGoal,
                serializedParsedFile,
                coqLspClient,
                logger
            );
        switch (requestType) {
            case TargetRequestType.THEOREM_PROOF:
                // THEOREM_PROOF goals are already parsed within the theorems,
                // so `ParsedFileTarget`-s for them are redundant
                return [];
            case TargetRequestType.ALL_ADMITS:
                const parsedTargets = [];
                for (const holeProofStep of theorem.proof!.holes) {
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

    async function buildParsedFileTarget(
        proofStep: SerializedProofStep,
        targetType: TargetType,
        theoremName: string,
        knownGoal: SerializedGoal | undefined,
        serializedParsedFile: SerializedParsedCoqFile,
        coqLspClient: CoqLspClientInterface,
        logger: Logger
    ): Promise<Signature.ResultModels.ParsedFileTarget> {
        let serializedGoal = knownGoal;
        if (serializedGoal === undefined) {
            const goals = await coqLspClient.getGoalsAtPoint(
                proofStep.range.start,
                Uri.fromPath(serializedParsedFile.filePath),
                serializedParsedFile.fileVersion
            );
            const startPosition = deserializeCodeElementPosition(
                proofStep.range.start
            );
            if (goals.err) {
                const goal = goals.val;
                const stack = goal.stack === undefined ? "" : `\n${goal.stack}`;
                logger.error(
                    `Failed to retrieve target goal at point: "${goal.message}" at ${startPosition}, "${serializedParsedFile.filePath}"${stack}`
                );
                throw goal;
            } else {
                const goal = goals.val[0];
                logger.debug(
                    `Successfully retrieved target goal at point: "${goal.ty}" at ${startPosition}, "${serializedParsedFile.filePath}"`
                );
                serializedGoal = serializeGoal(goal);
            }
        }

        return {
            theoremName: theoremName,
            targetType: targetType,
            goalToProve: serializedGoal,
            positionRange: proofStep.range,
        };
    }
}
