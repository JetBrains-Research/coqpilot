export class EventLogger {
    events: { [key: string]: Array<(data: string) => void> };

    constructor() {
        this.events = {};
    }

    subscribe(event: string, callback: (data: string) => void): void {
        if (this.events[event] === undefined) {
            this.events[event] = [];
        }
        this.events[event].push(callback);
    }

    log(event: string, data: string): void {
        if (this.events[event] !== undefined) {
            for (const callback of this.events[event]) {
                callback(data);
            }
        }
    }
}