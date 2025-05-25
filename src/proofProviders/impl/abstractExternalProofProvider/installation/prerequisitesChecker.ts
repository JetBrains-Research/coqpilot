import { exec } from "child_process";

import { InstallationFailedError } from "./installationFailedError";

export interface InstallationPrerequisite {
    name: string;
    checkCommand: string;
}

export async function checkAbstractPrerequisiteOrThrow(
    installationTargetName: string,
    prerequisite: InstallationPrerequisite
) {
    return new Promise<void>((resolve, reject) => {
        exec(prerequisite.checkCommand, (error) => {
            if (error) {
                reject(
                    new InstallationFailedError(
                        `missing prerequisite \`${prerequisite.name}\` for ${installationTargetName} installation`,
                        `${installationTargetName} requires "${prerequisite.name}", but it wasn't found (check command failed: \`${prerequisite.checkCommand}\`). Please ensure "${prerequisite.name}" is installed and try again.`
                    )
                );
            } else {
                resolve();
            }
        });
    });
}

export async function checkAbstractPrerequisitesOrThrow(
    installationTargetName: string,
    prerequisites: InstallationPrerequisite[]
) {
    for (const prerequisite of prerequisites) {
        await checkAbstractPrerequisiteOrThrow(
            installationTargetName,
            prerequisite
        );
    }
}
