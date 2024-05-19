export enum Severity {
    LOGIC,
    INFO,
    DEBUG,
}

export const anyEventKeyword = "any";

export type SubscriptionId = number;

interface EventSubscription {
    id: SubscriptionId;
    callback: (message: string, data?: any) => void;
    severity: Severity;
}

export class EventLogger {
    private events: {
        [key: string]: Array<EventSubscription>;
    };

    private newSubscriptionId: SubscriptionId = 0;

    constructor() {
        this.events = {};
    }

    subscribe(
        event: string,
        severity: Severity,
        callback: (message: string, data?: any) => void
    ): SubscriptionId {
        if (this.events[event] === undefined) {
            this.events[event] = [];
        }
        this.events[event].push({
            id: this.newSubscriptionId,
            callback,
            severity,
        });
        return this.newSubscriptionId++;
    }

    unsubscribe(event: string, subscriptionId: SubscriptionId) {
        this.events[event] = this.events[event]?.filter((eventSubscription) => {
            eventSubscription.id !== subscriptionId;
        });
    }

    log(
        event: string,
        message: string,
        data?: any,
        severity: Severity = Severity.INFO
    ) {
        this.events[event]?.forEach((eventSubscription) => {
            if (eventSubscription.severity === severity) {
                eventSubscription.callback(message, data);
            }
        });

        this.events[anyEventKeyword]?.forEach((eventSubscription) => {
            if (eventSubscription.severity === severity) {
                eventSubscription.callback(message, data);
            }
        });
    }

    subscribeToLogicEvent(
        event: string,
        callback: (data?: any) => void
    ): SubscriptionId {
        return this.subscribe(event, Severity.LOGIC, (_message, data) =>
            callback(data)
        );
    }

    logLogicEvent(event: string, data?: any) {
        this.log(event, "", data, Severity.LOGIC);
    }
}
