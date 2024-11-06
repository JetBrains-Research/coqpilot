import { createTestCoqLspClient } from "../../coqLsp/coqLspBuilders";

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
    const client = await createTestCoqLspClient(rootDir);

    await client.openTextDocument(fileUri);
    const abortController = new AbortController();
    const document = await parseCoqFile(
        fileUri,
        client,
        abortController.signal
    );
    await client.closeTextDocument(fileUri);

    return document;
}
