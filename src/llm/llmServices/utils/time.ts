export function nowTimestampMillis(): number {
    return new Date().getTime();
}

export type TimeUnit = "second" | "minute" | "hour" | "day";

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
        1000
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

function timeInUnitsToMillis(value: number, unit: TimeUnit = "second"): number {
    let result = value * 1000;
    switch (unit) {
        case "second":
            return result;
        case "minute":
            return result * 60;
        case "hour":
            return result * 60 * 60;
        case "day":
            return result * 60 * 60 * 24;
    }
}
