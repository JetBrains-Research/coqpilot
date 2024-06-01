export function nowTimestampMillis(): number {
    return new Date().getTime();
}

export type TimeUnit = "millisecond" | "second" | "minute" | "hour" | "day";

export interface Time {
    millis: number;
    seconds: number;
    minutes: number;
    hours: number;
    days: number;
}

export function millisToTime(totalMillis: number): Time {
    const totalSeconds = Math.floor(totalMillis / 1000);
    const totalMinutes = Math.floor(totalSeconds / 60);
    const totalHours = Math.floor(totalMinutes / 60);
    const totalDays = Math.floor(totalHours / 24);
    return {
        millis: totalMillis % 1000,
        seconds: totalSeconds % 60,
        minutes: totalMinutes % 60,
        hours: totalHours % 24,
        days: totalDays,
    };
}

export function timeToMillis(time: Time): number {
    return (
        (((time.hours + time.days * 24) * 60 + time.minutes) * 60 +
            time.seconds) *
            1000 +
        time.millis
    );
}

export function time(value: number, unit: TimeUnit): Time {
    return millisToTime(timeInUnitsToMillis(value, unit));
}

export const timeZero: Time = {
    millis: 0,
    seconds: 0,
    minutes: 0,
    hours: 0,
    days: 0,
};

export function timeToString(time: Time): string {
    if (time === timeZero) {
        return "0 ms";
    }
    const resolvedTime = millisToTime(timeToMillis(time));

    const days = `${resolvedTime.days} d`;
    const hours = `${resolvedTime.hours} h`;
    const minutes = `${resolvedTime.minutes} m`;
    const seconds = `${resolvedTime.seconds} s`;
    const millis = `${resolvedTime.millis} ms`;

    const orderedTimeItems = [
        [resolvedTime.days, days],
        [resolvedTime.hours, hours],
        [resolvedTime.minutes, minutes],
        [resolvedTime.seconds, seconds],
        [resolvedTime.millis, millis],
    ];
    const fromIndex = orderedTimeItems.findIndex(
        ([timeValue, _timeString]) => timeValue !== 0
    );
    const toIndex =
        orderedTimeItems.length -
        orderedTimeItems
            .reverse()
            .findIndex(([timeValue, _timeString]) => timeValue !== 0);

    return orderedTimeItems
        .reverse()
        .slice(fromIndex, toIndex)
        .map(([_timeValue, timeString]) => timeString)
        .join(", ");
}

export function millisToString(millis: number): string {
    return timeToString(millisToTime(millis));
}

function timeInUnitsToMillis(value: number, unit: TimeUnit = "second"): number {
    switch (unit) {
        case "millisecond":
            return value;
        case "second":
            return value * 1000;
        case "minute":
            return value * 1000 * 60;
        case "hour":
            return value * 1000 * 60 * 60;
        case "day":
            return value * 1000 * 60 * 60 * 24;
    }
}
