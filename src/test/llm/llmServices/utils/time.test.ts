import { expect } from "earl";

import {
    Time,
    millisToTime,
    time,
    timeToMillis,
} from "../../../../llm/llmServices/utils/time";

suite("[LLMService-s utils] Time utils test", () => {
    const zero: Time = {
        millis: 0,
        seconds: 0,
        minutes: 0,
        hours: 0,
        days: 0,
    };

    const fiveSeconds: Time = {
        millis: 0,
        seconds: 5,
        minutes: 0,
        hours: 0,
        days: 0,
    };

    const fiveSecondsInMillis: Time = {
        millis: 5000,
        seconds: 0,
        minutes: 0,
        hours: 0,
        days: 0,
    };

    const twoDays: Time = {
        millis: 0,
        seconds: 0,
        minutes: 0,
        hours: 0,
        days: 2,
    };

    const manyDays: Time = {
        millis: 0,
        seconds: 0,
        minutes: 0,
        hours: 0,
        days: 99999,
    };

    const mixedResolved: Time = {
        millis: 100,
        seconds: 40,
        minutes: 30,
        hours: 20,
        days: 10,
    };

    const mixedUnresolved: Time = {
        millis: 10100,
        seconds: 210,
        minutes: 147,
        hours: 66,
        days: 8,
    };

    test("Test `timeToMillis`", () => {
        expect(timeToMillis(zero)).toEqual(0);
        expect(timeToMillis(fiveSeconds)).toEqual(5000);
        expect(timeToMillis(fiveSecondsInMillis)).toEqual(5000);
        expect(timeToMillis(twoDays)).toEqual(2 * 24 * 60 * 60 * 1000);
    });

    test("Test `millisToTime`", () => {
        expect(millisToTime(0)).toEqual(zero);
        expect(millisToTime(5000)).toEqual(fiveSeconds);
        expect(millisToTime(2 * 24 * 60 * 60 * 1000)).toEqual(twoDays);
    });

    test("Test resolution through `millisToTime`", () => {
        expect(millisToTime(timeToMillis(twoDays))).toEqual(twoDays);
        expect(millisToTime(timeToMillis(manyDays))).toEqual(manyDays);
        expect(millisToTime(timeToMillis(mixedResolved))).toEqual(
            mixedResolved
        );
        expect(millisToTime(timeToMillis(mixedUnresolved))).toEqual(
            mixedResolved
        );
    });

    test("Test `time` factory", () => {
        expect(time(5, "second")).toEqual(fiveSeconds);
        expect(time(5000, "millisecond")).toEqual(fiveSeconds);
        expect(time(2, "day")).toEqual(twoDays);
        expect(time(2 * 24 * 60, "minute")).toEqual(twoDays);
    });
});
