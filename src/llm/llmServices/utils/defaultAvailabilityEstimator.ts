import { RequestsLogger } from "./requestsLogger/requestsLogger";
import {
    Time,
    millisToTime,
    nowTimestampMillis,
    time,
    timeToMillis,
    timeZero,
} from "./time";

export const defaultHeuristicEstimationsMillis = [
    time(5, "second"),
    time(10, "second"),
    time(30, "second"),
    time(1, "minute"),
    time(5, "minute"),
    time(10, "minute"),
    time(30, "minute"),
    time(1, "hour"),
    time(1, "day"),
].map((time) => timeToMillis(time));

/**
 * Estimates the expected time for service to become available.
 * To do this, analyzes the logs from `requestsLogger` and computes the time.
 * The default algorithm does the following:
 * - if the last attempt is successful => don't wait;
 * - if there is only one failed attemp => wait 1 second;
 * - otherwise, find the maximum time interval between two consistent failures;
 *   - then, find the first heuristical time estimation that is greater than it;
 *   - return the difference between this estimation and the time since last attempt
 *   - (if the time since last attempt is greater => there is no need to wait).
 */
export function estimateTimeToBecomeAvailableDefault(
    requestsLogger: RequestsLogger
): Time {
    const [_lastSuccess, ...failures] =
        requestsLogger.readLogsSinceLastSuccess();

    if (failures.length === 0) {
        return timeZero;
    }
    if (failures.length === 1) {
        return time(1, "second");
    }

    const intervals: number[] = [];
    for (let i = 1; i < failures.length; i++) {
        intervals.push(
            failures[i].timestampMillis - failures[i - 1].timestampMillis
        );
    }
    const maxInterval = Math.max(...intervals);
    let currentEstimationIndex = 0;
    while (
        currentEstimationIndex < defaultHeuristicEstimationsMillis.length &&
        maxInterval >= defaultHeuristicEstimationsMillis[currentEstimationIndex]
    ) {
        currentEstimationIndex++;
    }
    const currentEstimation =
        defaultHeuristicEstimationsMillis[currentEstimationIndex];

    const timeFromLastAttempt =
        nowTimestampMillis() - failures[failures.length - 1].timestampMillis;

    if (timeFromLastAttempt < currentEstimation) {
        return millisToTime(currentEstimation - timeFromLastAttempt);
    }
    return timeZero;
}
