import { createDirectory } from "./directoryUtils";
import { joinPaths } from "./pathUtils";

export const COQPILOT_META_DIR_NAME = ".coqpilot";
export const COQPILOT_META_LOGS_SUBDIR_NAME = "logs";

export function getCoqPilotMetaDirPath(projectRootPath: string): string {
    return joinPaths(projectRootPath, COQPILOT_META_DIR_NAME);
}

export function getOrCreateCoqPilotMetaDir(projectRootPath: string): string {
    return createDirectory(false, projectRootPath, COQPILOT_META_DIR_NAME);
}

export function getOrCreateCoqPilotMetaLogsDir(
    projectRootPath: string
): string {
    return createDirectory(
        false,
        getCoqPilotMetaDirPath(projectRootPath),
        COQPILOT_META_LOGS_SUBDIR_NAME
    );
}
