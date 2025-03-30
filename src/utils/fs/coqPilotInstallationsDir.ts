import { homedir } from "os";

import { createDirectory } from "./directoryUtils";
import { joinPaths } from "./pathUtils";

export const COQPILOT_INSTALLATIONS_DIR_NAME = ".coqpilot-installations";

export function getCoqPilotInstallationsDirPath(): string {
    return joinPaths(homedir(), COQPILOT_INSTALLATIONS_DIR_NAME);
}

export function getOrCreateCoqPilotInstallationsDir(): string {
    return createDirectory(false, getCoqPilotInstallationsDirPath());
}
