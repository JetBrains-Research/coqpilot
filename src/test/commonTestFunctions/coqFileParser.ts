import { withDocumentOpenedByTestCoqLsp } from "../../coqLsp/coqLspBuilders";

import { parseCoqFile } from "../../coqParser/parseCoqFile";
import { Theorem } from "../../coqParser/parsedTypes";
import { Uri } from "../../utils/uri";

import { resolveResourcesDir } from "./pathsResolver";

export async function parseTheoremsFromCoqFile(
    resourcePath: string[],
    projectRootPath?: string[]
): Promise<Theorem[]> {
    const [filePath, rootDir] = resolveResourcesDir(
        resourcePath,
        projectRootPath
    );
    const fileUri = Uri.fromPath(filePath);

    return await withDocumentOpenedByTestCoqLsp(
        { uri: fileUri },
        { workspaceRootPath: rootDir },
        (coqLspClient) =>
            parseCoqFile(fileUri, coqLspClient, new AbortController().signal)
    );
}
