import { ResolveType } from "./promiseUtils";

export class AsyncScheduler {
    private readonly schedulerLogsIdentifier: string;

    constructor(
        private readonly maxRunningTasksNumber: number,
        private readonly enableSchedulingDebugLogs: boolean = false,
        schedulerName: string = "Async Scheduler"
    ) {
        this.schedulerLogsIdentifier = `[${schedulerName}] `;
    }

    private runningTasksNumber: number = 0;
    private readonly pendingTasksLocks: ResolveType<void>[] = [];

    scheduleTask<T>(
        executeTask: () => Promise<T>,
        onDebugLog: (message: string) => void
    ): Promise<T> {
        const debugLog: (...messages: string[]) => void = (
            ...messages: string[]
        ) => {
            if (this.enableSchedulingDebugLogs) {
                onDebugLog(
                    `${this.schedulerLogsIdentifier}${messages.join("\n")}`
                );
            }
        };
        let startLock: Promise<void> = new Promise((resolve, reject) => {
            if (this.runningTasksNumber < this.maxRunningTasksNumber) {
                debugLog(
                    "Starting task execution immediately",
                    `Increased number of running tasks: ${this.runningTasksNumber} --> ${this.runningTasksNumber + 1}`
                );
                this.runningTasksNumber += 1;
                reject(); // reject is called here to differentiate immediate and pending lock resolutions
            } else {
                debugLog(
                    `Maximum number of running tasks (${this.maxRunningTasksNumber}) is already reached (${this.runningTasksNumber}), waiting for some of them to finish`
                );
                this.pendingTasksLocks.push(resolve);
            }
        });
        const executeTaskAndScheduleNext: () => Promise<T> = () =>
            executeTask().finally(() => {
                const resolveNextTaskLock = this.pendingTasksLocks.shift();
                if (resolveNextTaskLock === undefined) {
                    debugLog(
                        "Task execution finished, there are no pending tasks",
                        `Decreased number of running tasks: ${this.runningTasksNumber} --> ${this.runningTasksNumber - 1}`
                    );
                    this.runningTasksNumber -= 1;
                } else {
                    debugLog(
                        "Task execution finished, starting the next pending one"
                    );
                    resolveNextTaskLock();
                }
            });
        return startLock
            .then(() =>
                debugLog(
                    "Finished waiting in the pending-tasks queue, starting the execution"
                )
            )
            .then(executeTaskAndScheduleNext, executeTaskAndScheduleNext);
    }
}
