import {
    Disposable
} from 'vscode';

export class NotificationService implements Disposable {
    private _timer: NodeJS.Timeout | null;
    private _timeout = 2000;
    private _action: () => void;

    constructor(action: () => void) {
        this._timer = null;
        this._action = action;
    }

    onNotificationReceived() {
        this._clearTimer();

        // Reset the timer
        this._timer = setTimeout(() => {
            this._action();
            this._timer = null;
        }, this._timeout);
    }

    private _clearTimer() {
        if (this._timer) {
            clearTimeout(this._timer);
            this._timer = null;
        }
    }

    dispose() {
        this._clearTimer();
    }
}