import { ProofGoal } from "../../../../coqLsp/coqLspTypes";

import { TargetType } from "../../structures/completionGenerationTask";
import {
    ParsedCoqFileData,
    deserializeParsedCoqFile,
} from "../../structures/parsedCoqFileData";
import { TheoremData } from "../../structures/theoremData";
import {
    CodeElementRange,
    deserializeCodeElementRange,
} from "../../structures/utilStructures";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../../subprocessCalls/buildAndParseCoqProject/callSignature";
import { deserializeGoal } from "../../utils/goalParser";

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

    parsedFilesNumber(): number {
        return this.filePathToFileHolder.size;
    }

    entries(): [string, ParsedFileHolder][] {
        return Array.from(this.filePathToFileHolder.entries());
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

    parsedFile(): ParsedCoqFileData {
        return this.parsedFileData;
    }

    targets(): ParsedFileTarget[] {
        return this.fileTargets;
    }
}

export class ParsedFileTarget {
    readonly sourceTheorem: TheoremData;
    readonly targetType: TargetType;
    readonly goalToProve: ProofGoal;
    readonly positionRange: CodeElementRange;

    constructor(
        rawParsedFileTarget: Signature.ResultModels.ParsedFileTarget,
        parsedFileData: ParsedCoqFileData
    ) {
        this.sourceTheorem = parsedFileData.theoremsByNames.get(
            rawParsedFileTarget.theoremName
        )!;
        this.targetType = rawParsedFileTarget.targetType;
        this.goalToProve = deserializeGoal(rawParsedFileTarget.goalToProve);
        this.positionRange = deserializeCodeElementRange(
            rawParsedFileTarget.positionRange
        );
    }
}
