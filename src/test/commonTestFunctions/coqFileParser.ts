import { parseCoqFile } from "../../coqParser/parseCoqFile";
import { Theorem } from "../../coqParser/parsedTypes";
import { Uri } from "../../utils/uri";

import { createCoqLspClient } from "./coqLspBuilder";
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
    const client = await createCoqLspClient(rootDir);

    await client.openTextDocument(fileUri);
    const document = await parseCoqFile(fileUri, client);
    await client.closeTextDocument(fileUri);

    return document;
}
