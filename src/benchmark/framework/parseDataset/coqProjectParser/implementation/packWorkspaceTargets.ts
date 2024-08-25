import {
    AllTheoremsTarget,
    SpecificTheoremTarget,
    WorkspaceInputTargets,
} from "../../../structures/inputTargets";
import { entriesToMappedObject } from "../../../utils/mapUtils";

import { ParseCoqProjectInternalSignature } from "./internalSignature";

export namespace CoqProjectParserUtils {
    import Signature = ParseCoqProjectInternalSignature;

    export function packWorkspaceTargets(
        missingTargets: WorkspaceInputTargets
    ): Signature.ArgsModels.FilePathToFileTargets {
        const mappedEntries: [string, Signature.ArgsModels.FileTarget[]][] =
            missingTargets.entries().map(([filePath, fileTargets]) => {
                return [
                    filePath,
                    fileTargets.map((fileTarget) => {
                        if (fileTarget instanceof AllTheoremsTarget) {
                            return {
                                requestType: fileTarget.requestType,
                                specificTheoremName: undefined,
                            };
                        } else if (
                            fileTarget instanceof SpecificTheoremTarget
                        ) {
                            return {
                                requestType: fileTarget.requestType,
                                specificTheoremName: fileTarget.theoremName,
                            };
                        } else {
                            throw Error(
                                `Unknown input file target: ${fileTarget.toString("", "")}`
                            );
                        }
                    }),
                ];
            });
        return entriesToMappedObject(mappedEntries);
    }
}
