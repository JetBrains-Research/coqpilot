/* eslint-disable @typescript-eslint/naming-convention */
export enum Severity {
    LOGIC = "LOGIC",
    INFO = "INFO",
    DEBUG = "DEBUG",
}

export const ALL_EVENTS = "all";
/* eslint-enable @typescript-eslint/naming-convention */

export class EventLogger {
    events: {
        [key: string]: Array<[(message: string, data?: any) => void, Severity]>;
    };

    constructor() {
        this.events = {};
    }

    subscribe(
        event: string,
        severity: Severity,
        callback: (message: string, data?: any) => void
    ): void {
        if (this.events[event] === undefined) {
            this.events[event] = [];
        }
        this.events[event].push([callback, severity]);
    }

    log(
        event: string,
        message: string,
        data?: any,
        severity: Severity = Severity.INFO
    ) {
        this.events[event]?.forEach(([callback, subscribedSeverity]) => {
            if (subscribedSeverity === severity) {
                callback(message, data);
            }
        });

        this.events[ALL_EVENTS]?.forEach(([callback, subscribedSeverity]) => {
            if (subscribedSeverity === severity) {
                callback(message, data);
            }
        });
    }

    logLogicEvent(event: string, data?: any) {
        this.log(event, "", data, Severity.LOGIC);
    }
}
