import { createSourceFileEnvironment } from "../../../../../core/inspectSourceFile";

import { Uri } from "../../../../../utils/uri";
import { SerializedParsedCoqFile } from "../../structures/parsedCoqFileData";
import { serializeTheorem } from "../../structures/theoremData";
import { createCoqLspClient } from "../../utils/coqLspUtils";
import {
    LogsIPCSender,
    executeAsFunctionOnParentProcessCall,
} from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/executeOnParentProcessCall";
import { subprocessExecutable } from "../../utils/subprocessUtils/ipc/onParentProcessCallExecutor/subprocessExecutableTestWrapper";

import { BuildAndParseCoqProjectBySubprocessSignature } from "./callSignature";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

subprocessExecutable(Signature.subprocessName, () =>
    executeAsFunctionOnParentProcessCall<Signature.Args, Signature.Result>(
        Signature.argsSchema,
        Signature.resultSchema,
        buildAndParseCoqProject
    )
);

async function buildAndParseCoqProject(
    args: Signature.Args,
    logger: LogsIPCSender
): Promise<Signature.Result> {
    const coqLspClient = createCoqLspClient(args.workspaceRootPath);
    const serializedParsedFiles: SerializedParsedCoqFile[] = [];
    for (const sourceFilePath of args.sourceFilesToParsePaths) {
        const mockFileVersion = 1;
        const sourceFileUri = Uri.fromPath(sourceFilePath);
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
            filePath: sourceFilePath,
        };
        logger.debug(
            `successfully parsed "${sourceFilePath}": found ${serializedParsedFile.allFileTheorems.length} theorems, read ${serializedParsedFile.fileLines.length} lines`
        );
        serializedParsedFiles.push(serializedParsedFile);
    }
    return serializedParsedFiles;
}
