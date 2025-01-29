import { colorize } from "../../../utils/colorLogging";

/**
 * Unlike `stdout`, writing to `stderr` is not usually suppressed, for example, by Mocha tests.
 * However, writing to `stderr` is synchronous and is usually not buffered,
 * which can cause performance degradation, be careful.
 */
export function writeToConsoleErr(message: string) {
    process.stderr.write(message);
}

export function writeSystemMessageToConsole(message: string) {
    writeToConsoleErr(
        colorize(`\n[Benchmarking - System Message]\n${message}\n`, "magenta")
    );
}

/**
 * Source: https://www.jetbrains.com/help/teamcity/service-messages.html#Reporting+Build+Statistics
 */
export function writeTeamCityStatisticsValue(key: string, value: number) {
    writeSystemMessageToConsole(
        `##teamcity[buildStatisticValue key='${key}' value='${value}']`
    );
}
