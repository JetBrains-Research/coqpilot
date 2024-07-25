import { createTestCoqLspClient } from "../../../../../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../../../../../coqLsp/coqLspClient";

import { createSourceFileEnvironment } from "../../../../../core/inspectSourceFile";

import { TargetType } from "../../../../../benchmark/framework/structures/completionGenerationTask";
import { TargetRequestType } from "../../../../../benchmark/framework/structures/inputTargets";
import { SerializedParsedCoqFile } from "../../../../../benchmark/framework/structures/parsedCoqFileData";
import {
    SerializedProofStep,
    SerializedTheorem,
    TheoremData,
    serializeTheoremData,
} from "../../../../../benchmark/framework/structures/theoremData";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../../../../../benchmark/framework/subprocessCalls/buildAndParseCoqProject/callSignature";
import { serializeGoal } from "../../../../../benchmark/framework/utils/goalParser";
import {
    mappedObjectValues,
    packIntoMappedObject,
} from "../../../../../benchmark/framework/utils/mapUtils";
import { extractSerializedTheoremFisrtProofStep } from "../../../../../benchmark/framework/utils/proofTargetExtractor";
import { executeAsFunctionOnParentProcessCall } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { LogsIPCSender } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/logsIpcSender";
import { subprocessExecutable } from "../../../../../benchmark/framework/utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";
import { Uri } from "../../../../../utils/uri";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

subprocessExecutable(Signature.subprocessName, () =>
    executeAsFunctionOnParentProcessCall<
        Signature.ArgsModels.Args,
        Signature.ResultModels.Result
    >(
        Signature.ArgsModels.argsSchema,
        Signature.ResultModels.resultSchema,
        buildAndParseCoqProject
    )
);

async function buildAndParseCoqProject(
    args: Signature.ArgsModels.Args,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.Result> {
    const coqLspClient = createTestCoqLspClient(args.workspaceRootPath);
    const parsedWorkspace: Signature.ResultModels.Result = {};
    for (const filePath in args.workspaceTargets) {
        const fileTargets = args.workspaceTargets[filePath];
        const serializedParsedFile = await openAndParseSourceFile(
            filePath,
            coqLspClient,
            logger
        );
        const parsedFileResults: Signature.ResultModels.ParsedFileResults = {
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
    // TODO: use proper logging
    console.error(
        `Successfully parsed Coq project: analyzed ${Object.keys(parsedWorkspace).length} files`
    );
    return parsedWorkspace;
}

async function openAndParseSourceFile(
    filePath: string,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<SerializedParsedCoqFile> {
    const mockFileVersion = 1;
    const sourceFileUri = Uri.fromPath(filePath);
    await coqLspClient.openTextDocument(sourceFileUri);
    const sourceFileEnvironment = await createSourceFileEnvironment(
        mockFileVersion,
        sourceFileUri,
        coqLspClient
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
    logger.debug(
        `Successfully parsed "${filePath}": found ${serializedParsedFile.serializedTheoremsByNames.length} theorems, read ${serializedParsedFile.fileLines.length} lines`
    );
    return serializedParsedFile;
}

async function extractFileTargetsFromFile(
    fileTargets: Signature.ArgsModels.FileTarget[],
    serializedParsedFile: SerializedParsedCoqFile,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.ParsedFileTarget[]> {
    const parsedTargetsSets: Signature.ResultModels.ParsedFileTarget[][] = [];
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
            const parsedTargetsFromTheorem = await extractTargetsFromTheorem(
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
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.ParsedFileTarget[]> {
    const targetBuilder: (
        proofStep: SerializedProofStep,
        targetType: TargetType
    ) => Promise<Signature.ResultModels.ParsedFileTarget> = (
        proofStep,
        targetType
    ) =>
        buildParsedFileTarget(
            proofStep,
            targetType,
            theorem.name,
            serializedParsedFile,
            coqLspClient,
            logger
        );
    switch (requestType) {
        case TargetRequestType.ALL_ADMITS:
            const parsedTargets = [];
            for (const holeProofStep of theorem.proof!.holes) {
                parsedTargets.push(
                    await targetBuilder(holeProofStep, TargetType.ADMIT)
                );
            }
            return parsedTargets;
        case TargetRequestType.THEOREM_PROOF:
            const firstProofStep =
                extractSerializedTheoremFisrtProofStep(theorem);
            return [
                await targetBuilder(firstProofStep, TargetType.PROVE_THEOREM),
            ];
    }
}

async function buildParsedFileTarget(
    proofStep: SerializedProofStep,
    targetType: TargetType,
    theoremName: string,
    serializedParsedFile: SerializedParsedCoqFile,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.ParsedFileTarget> {
    const goal = await coqLspClient.getFirstGoalAtPoint(
        proofStep.range.start,
        Uri.fromPath(serializedParsedFile.filePath),
        serializedParsedFile.fileVersion
    );
    if (goal instanceof Error) {
        const stack = goal.stack === undefined ? "" : `\n${goal.stack}`;
        logger.error(
            `Failed to retrieve target goal at point: "${goal.message}" at ${proofStep.range.start}, "${serializedParsedFile.filePath}"${stack}`
        );
        throw goal;
    } else {
        logger.debug(
            `Successfully retrieved target goal at point: "${goal.ty}" at ${proofStep.range.start}, "${serializedParsedFile.filePath}"`
        );
    }
    return {
        theoremName: theoremName,
        targetType: targetType,
        goalToProve: serializeGoal(goal),
        positionRange: proofStep.range,
    };
}
