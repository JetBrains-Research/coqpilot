import { exec } from "child_process";

import { EditorMessages } from "../ui/messages/editorMessages";

import { InstallationFailedError } from "./installationFailedError";

export interface InstallationPrerequisite {
    name: string;
    checkCommand: string;
}

export async function checkPrerequisiteOrThrow(
    installationTargetName: string,
    prerequisite: InstallationPrerequisite
) {
    return new Promise<void>((resolve, reject) => {
        exec(prerequisite.checkCommand, (error) => {
            if (error) {
                reject(
                    new InstallationFailedError(
                        `missing prerequisite \`${prerequisite.name}\` for ${installationTargetName} installation`,
                        EditorMessages.installationPrerequisiteIsMissing(
                            installationTargetName,
                            prerequisite
                        )
                    )
                );
            } else {
                resolve();
            }
        });
    });
}

export async function checkPrerequisitesOrThrow(
    installationTargetName: string,
    prerequisites: InstallationPrerequisite[]
) {
    for (const prerequisite of prerequisites) {
        await checkPrerequisiteOrThrow(installationTargetName, prerequisite);
    }
}
