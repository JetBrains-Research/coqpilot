import { CoqLspClient } from "../../../../../coqLsp/coqLspClient";

import { createSourceFileEnvironment } from "../../../../../core/inspectSourceFile";

import { Uri } from "../../../../../utils/uri";
import { SerializedParsedCoqFile } from "../../structures/parsedCoqFileData";
import {
    SerializedProofStep,
    SerializedTheorem,
    serializeTheorem,
} from "../../structures/theoremData";
import { createCoqLspClient } from "../../utils/coqLspUtils";
import {
    LogsIPCSender,
    executeAsFunctionOnParentProcessCall,
} from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { subprocessExecutable } from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

import { BuildAndParseCoqProjectBySubprocessSignature } from "./callSignature";

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
    const coqLspClient = createCoqLspClient(args.workspaceRootPath);
    const parsedFileTargets: Signature.ResultModels.Result = {};
    for (const filePath in args.sourceFilePathToTarget) {
        const fileTarget = args.sourceFilePathToTarget[filePath];
        const serializedParsedFile = await parseSourceFile(
            filePath,
            coqLspClient,
            logger
        );
        const parsedFileTarget: Signature.ResultModels.ParsedFileTarget = {
            serializedParsedFile: serializedParsedFile,
            extractedTaskTargets: await extractTaskTargetsFromFile(
                fileTarget,
                serializedParsedFile,
                coqLspClient,
                logger
            ),
        };
        parsedFileTargets[filePath] = parsedFileTarget;
    }
    // TODO: add successful log report maybe
    return parsedFileTargets;
}

async function parseSourceFile(
    filePath: string,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<SerializedParsedCoqFile> {
    const mockFileVersion = 1;
    const sourceFileUri = Uri.fromPath(filePath);
    const sourceFileEnvironment = await createSourceFileEnvironment(
        mockFileVersion,
        sourceFileUri,
        coqLspClient
    );
    const serializedParsedFile: SerializedParsedCoqFile = {
        allFileTheorems:
            sourceFileEnvironment.fileTheorems.map(serializeTheorem),
        fileLines: sourceFileEnvironment.fileLines,
        fileVersion: sourceFileEnvironment.fileVersion,
        filePath: filePath,
    };
    logger.debug(
        `successfully parsed "${filePath}": found ${serializedParsedFile.allFileTheorems.length} theorems, read ${serializedParsedFile.fileLines.length} lines`
    );
    return serializedParsedFile;
}

async function extractTaskTargetsFromFile(
    fileTarget: Signature.ArgsModels.FileTarget,
    serializedParsedFile: SerializedParsedCoqFile,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.TaskTarget[]> {
    const taskTargets: Signature.ResultModels.TaskTarget[] = [];

    // construct all theorems targets
    for (const targetType of fileTarget.allTheoremsTargetTypes) {
        for (let i = 0; i < serializedParsedFile.allFileTheorems.length; i++) {
            const theorem = serializedParsedFile.allFileTheorems[i];
            const taskTargets = await extractTaskTargetsFromTheorem(
                theorem,
                i,
                targetType,
                serializedParsedFile,
                coqLspClient,
                logger
            );
            taskTargets.forEach((taskTarget) => taskTargets.push(taskTarget));
        }
    }

    // construct specific theorems targets
    const theoremNameToTheoremWithIndex: Map<
        string,
        [SerializedTheorem, number]
    > = new Map(
        serializedParsedFile.allFileTheorems.map((serializedTheorem, i) => [
            serializedTheorem.name,
            [serializedTheorem, i],
        ])
    );
    for (const theoremName in fileTarget.specificTheoremTargets) {
        const theoremTarget = fileTarget.specificTheoremTargets[theoremName];
        const theoremWithIndex = theoremNameToTheoremWithIndex.get(theoremName);
        if (theoremWithIndex === undefined) {
            throw Error(
                `no parsed theorem data for requested theorem "${theoremName}" of "${serializedParsedFile.filePath}" file`
            );
        }
        const [theorem, theoremIndex] = theoremWithIndex;
        for (const targetType of theoremTarget.targetTypes) {
            const taskTargets = await extractTaskTargetsFromTheorem(
                theorem,
                theoremIndex,
                targetType,
                serializedParsedFile,
                coqLspClient,
                logger
            );
            taskTargets.forEach((taskTarget) => taskTargets.push(taskTarget));
        }
    }

    return taskTargets;
}

async function extractTaskTargetsFromTheorem(
    theorem: SerializedTheorem,
    sourceTheoremIndex: number,
    targetType: Signature.CommonModels.TargetType,
    serializedParsedFile: SerializedParsedCoqFile,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.TaskTarget[]> {
    switch (targetType) {
        case "ADMIT":
            const taskTargets = [];
            for (const holeProofStep of theorem.proof!.holes) {
                taskTargets.push(
                    await buildTaskTarget(
                        holeProofStep,
                        sourceTheoremIndex,
                        targetType,
                        serializedParsedFile,
                        coqLspClient,
                        logger
                    )
                );
            }
            return taskTargets;
        case "PROVE_THEOREM":
            const firstProofStep = theorem.proof!.proof_steps[1];
            return [
                await buildTaskTarget(
                    firstProofStep,
                    sourceTheoremIndex,
                    targetType,
                    serializedParsedFile,
                    coqLspClient,
                    logger
                ),
            ];
    }
}

async function buildTaskTarget(
    proofStep: SerializedProofStep,
    sourceTheoremIndex: number,
    targetType: Signature.CommonModels.TargetType,
    serializedParsedFile: SerializedParsedCoqFile,
    coqLspClient: CoqLspClient,
    logger: LogsIPCSender
): Promise<Signature.ResultModels.TaskTarget> {
    const goal = await coqLspClient.getFirstGoalAtPoint(
        proofStep.range.start,
        Uri.fromPath(serializedParsedFile.filePath),
        serializedParsedFile.fileVersion
    );
    if (goal instanceof Error) {
        const stack = goal.stack === undefined ? "" : `\n${goal.stack}`;
        logger.error(
            `failed to retrieve target goal at point: "${goal.message}" at ${proofStep.range.start}, "${serializedParsedFile.filePath}"${stack}`
        );
        throw goal;
    } else {
        logger.debug(
            `successfully retrieved target goal at point: "${goal.ty}" at ${proofStep.range.start}, "${serializedParsedFile.filePath}"`
        );
    }
    return {
        targetGoalToProve: JSON.stringify(goal), // TODO: come up with better (de)serialization
        targetPositionRange: proofStep.range,
        targetType: targetType,
        sourceTheoremIndex: sourceTheoremIndex,
    };
}
