import { buildErrorCompleteLog } from "../../utils/errors/errorsUtils";
import { illegalState } from "../../utils/errors/throwErrors";
import { readFile } from "../../utils/fs/fileUtils";
import { joinPaths } from "../../utils/fs/pathUtils";
import { getRootDir } from "../../utils/fs/rootResolvers";

export const PLUGIN_ID = "coqpilot";
export const PLUGIN_NAME = "CoqPilot";

const packageJsonPath = joinPaths(getRootDir(), "package.json");
const packageJson = JSON.parse(
    readFile(packageJsonPath, (err) =>
        illegalState(
            "failed to parse CoqPilot version: ",
            buildErrorCompleteLog(err)
        )
    )
);

export const PLUGIN_VERSION = packageJson.version;
