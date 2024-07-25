import { Goal, PpString } from "../../../coqLsp/coqLspTypes";

import { TargetType } from "../structures/completionGenerationTask";
import {
    ParsedCoqFileData,
    deserializeParsedCoqFile,
} from "../structures/parsedCoqFileData";
import { TheoremData } from "../structures/theoremData";
import {
    CodeElementRange,
    deserializeCodeElementRange,
} from "../structures/utilStructures";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";

import Signature = BuildAndParseCoqProjectBySubprocessSignature;

export class ParsedWorkspaceHolder {
    private readonly filePathToFileHolder: Map<string, ParsedFileHolder>;

    constructor(parsedWorkspace: Signature.ResultModels.Result) {
        this.filePathToFileHolder = new Map();
        for (const filePath in parsedWorkspace) {
            const parsedFileResults = parsedWorkspace[filePath];
            this.filePathToFileHolder.set(
                filePath,
                new ParsedFileHolder(parsedFileResults)
            );
        }
    }
}

export class ParsedFileHolder {
    private readonly parsedFileData: ParsedCoqFileData;
    private readonly fileTargets: ParsedFileTarget[];

    constructor(parsedFileResults: Signature.ResultModels.ParsedFileResults) {
        this.parsedFileData = deserializeParsedCoqFile(
            parsedFileResults.serializedParsedFile
        );
        this.fileTargets = parsedFileResults.parsedFileTargets.map(
            (rawParsedFileTarget) =>
                new ParsedFileTarget(rawParsedFileTarget, this.parsedFileData)
        );
    }
}

export class ParsedFileTarget {
    private readonly sourceTheorem: TheoremData;
    private readonly targetType: TargetType;
    private readonly goalToProve: Goal<PpString>;
    private readonly positionRange: CodeElementRange;

    constructor(
        rawParsedFileTarget: Signature.ResultModels.ParsedFileTarget,
        parsedFileData: ParsedCoqFileData
    ) {
        this.sourceTheorem = parsedFileData.theoremsByNames.get(
            rawParsedFileTarget.theoremName
        )!;
        this.targetType = rawParsedFileTarget.targetType;
        this.goalToProve = JSON.parse(
            rawParsedFileTarget.goalToProve
        ) as Goal<PpString>;
        this.positionRange = deserializeCodeElementRange(
            rawParsedFileTarget.positionRange
        );
    }
}
