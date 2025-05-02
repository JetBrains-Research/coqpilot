import { Uri } from "./uri";

export interface ProjectRoot {
    uri: Uri;
    requiresNixEnvironment: boolean;
}

export function stringifyProjectRoot(
    projectRoot: ProjectRoot | undefined
): string {
    if (projectRoot === undefined) {
        return "undefined";
    }
    return `{ path: ${projectRoot.uri.fsPath}, nix: ${projectRoot.requiresNixEnvironment} }`;
}
