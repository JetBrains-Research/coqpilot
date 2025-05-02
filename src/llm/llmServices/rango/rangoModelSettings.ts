import { resolvePossiblyRelativeAsAbsolutePath } from "../../../utils/fs/pathUtils";
import { RangoModelMode, RangoModelParams } from "../modelParams";

export interface RangoModelSettings {
    mode: RangoModelMode;
    timeoutSeconds: number;
    enableWholeProjectDataPoints: boolean;
    dataLocDirectoryPath: string;

    localCheckpointPath?: string;
    mappedToRemotePort?: number;
}

export function buildRangoModelSettingsFromParams(
    params: RangoModelParams,
    rangoDirPath: string
): RangoModelSettings {
    const commonParams = {
        mode: params.mode,
        timeoutSeconds: params.timeoutSeconds,
        enableWholeProjectDataPoints: params.enableWholeProjectDataPoints,
        dataLocDirectoryPath: params.dataLocDirectoryPath,
    };
    switch (params.mode) {
        case "local":
            return {
                ...commonParams,
                localCheckpointPath: resolvePossiblyRelativeAsAbsolutePath(
                    params.localCheckpointPath,
                    rangoDirPath
                ),
            };
        case "remote":
            return {
                ...commonParams,
                mappedToRemotePort: params.mappedToRemotePort,
            };
        case "mockOpenAI":
            return commonParams;
    }
}
