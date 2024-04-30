import { expect } from "earl";

import { estimateTimeToBecomeAvailableDefault } from "../../../../llm/llmServices/utils/defaultAvailabilityEstimator";
import {
    LoggerRecord,
    ResponseStatus,
} from "../../../../llm/llmServices/utils/requestsLogger/loggerRecord";
import {
    Time,
    nowTimestampMillis,
    time,
    timeToMillis,
    timeToString,
    timeZero,
} from "../../../../llm/llmServices/utils/time";

suite("[LLMService] Test default availability estimator", () => {
    function buildBasicRecord(
        timestampMillis: number,
        responseStatus: ResponseStatus
    ): LoggerRecord {
        return new LoggerRecord(
            timestampMillis,
            "test model",
            responseStatus,
            5,
            undefined,
            responseStatus === "FAILED"
                ? {
                      typeName: Error.name,
                      message: "connection error",
                  }
                : undefined
        );
    }

    function buildNextFailureRecord(
        timeDelta: Time,
        prevRecord: LoggerRecord
    ): LoggerRecord {
        return buildBasicRecord(
            prevRecord.timestampMillis + timeToMillis(timeDelta),
            "FAILED"
        );
    }

    function testAvailabilityEstimation(
        logs: LoggerRecord[],
        expectedEstimation: Time,
        nowMillis: number = nowTimestampMillis()
    ) {
        const actualEstimation = estimateTimeToBecomeAvailableDefault(
            logs,
            nowMillis
        );
        expect(actualEstimation).toEqual(expectedEstimation);
    }

    const startMillis = nowTimestampMillis();
    const startSuccess = buildBasicRecord(startMillis, "SUCCESS");

    test("No failures", () => {
        testAvailabilityEstimation([startSuccess], timeZero);
    });

    [time(100, "millisecond"), time(1, "second"), time(1, "day")].forEach(
        (failureTimeDelta) => {
            test(`Single failure in <${timeToString(failureTimeDelta)}>`, () => {
                const failure = buildNextFailureRecord(
                    failureTimeDelta,
                    startSuccess
                );
                testAvailabilityEstimation(
                    [startSuccess, failure],
                    time(1, "second")
                );
            });
        }
    );

    [
        [timeZero, timeZero, time(1, "second")], // check zero
        // check algorithm's logic
        [time(4, "minute"), timeZero, time(5, "minute")], // delay is expected to be > 4 minutes, the closest is 5 minutes
        [time(4, "minute"), time(1, "hour"), timeZero], // 5 minutes already passed (1 hour passed), no need to wait
        [time(4, "minute"), time(3, "minute"), time(2, "minute")], // 3 out of 5 minutes already passed, need to wait 2 more
        [time(4, "minute"), time(1, "second"), time(5, "minute")], // only 1 second passed, let's round estimation to 5 minutes still
        // check other heuristic estimations points
        [time(40, "minute"), timeZero, time(1, "hour")],
        [time(13, "hour"), timeZero, time(1, "day")],
        [time(2, "day"), timeZero, time(1, "day")], // check out-of-heuristic-estimations interval
    ].forEach(([interval, timeFromLastAttempt, expectedEstimate]) => {
        test(`Two failures with <${timeToString(interval)}> interval, <${timeToString(timeFromLastAttempt)}> from last attempt`, () => {
            const firstFailure = buildNextFailureRecord(
                time(1, "second"),
                startSuccess
            );
            const secondFailure = buildNextFailureRecord(
                interval,
                firstFailure
            );
            testAvailabilityEstimation(
                [startSuccess, firstFailure, secondFailure],
                expectedEstimate,
                secondFailure.timestampMillis +
                    timeToMillis(timeFromLastAttempt)
            );
        });
    });

    function buildFailureRecordsSequence(
        timeDeltas: Time[],
        startRecord: LoggerRecord
    ): LoggerRecord[] {
        const records = [startRecord];
        for (const timeDelta of timeDeltas) {
            records.push(
                buildNextFailureRecord(timeDelta, records[records.length - 1])
            );
        }
        return records;
    }

    test(`Many failures`, () => {
        const records = buildFailureRecordsSequence(
            [
                time(1, "second"),
                time(20, "second"),
                time(3, "minute"),
                time(1, "second"),
                time(1, "second"),
                time(4, "minute"), // max interval
                time(1, "minute"),
            ],
            startSuccess
        );
        testAvailabilityEstimation(
            records,
            time(5, "minute"), // max interval between failures is 4 minutes
            records[records.length - 1].timestampMillis // i.e. `timeFromLastAttempt` is 0
        );
    });

    test("Throw on invalid input logs", () => {
        expect(() =>
            estimateTimeToBecomeAvailableDefault([
                buildBasicRecord(startMillis, "FAILED"),
            ])
        ).toThrow();
        expect(() =>
            estimateTimeToBecomeAvailableDefault([
                startSuccess,
                buildBasicRecord(
                    startSuccess.timestampMillis + 1000,
                    "SUCCESS"
                ),
            ])
        ).toThrow();
    });
});
