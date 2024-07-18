import { BenchmarkingLogger } from "../logging/benchmarkingLogger";

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
        logger: BenchmarkingLogger
    ): Promise<T> {
        let startLock: Promise<void> = new Promise((resolve, reject) => {
            if (this.runningTasksNumber < this.maxRunningTasksNumber) {
                this.debugLog(
                    logger,
                    "Starting task execution immediately",
                    `Increased number of running tasks: ${this.runningTasksNumber} --> ${this.runningTasksNumber + 1}`
                );
                this.runningTasksNumber += 1;
                reject(); // reject is called here to differentiate immediate and pending lock resolutions
            } else {
                this.debugLog(
                    logger,
                    `Maximum number of running tasks (${this.maxRunningTasksNumber}) is already reached (${this.runningTasksNumber}), waiting for some of them to finish`
                );
                this.pendingTasksLocks.push(resolve);
            }
        });
        const executeTaskAndScheduleNext: () => Promise<T> = () =>
            executeTask().finally(() => {
                const resolveNextTaskLock = this.pendingTasksLocks.shift();
                if (resolveNextTaskLock === undefined) {
                    this.debugLog(
                        logger,
                        "Task execution finished, there are no pending tasks",
                        `Decreased number of running tasks: ${this.runningTasksNumber} --> ${this.runningTasksNumber - 1}`
                    );
                    this.runningTasksNumber -= 1;
                } else {
                    this.debugLog(
                        logger,
                        "Task execution finished, starting the next pending one"
                    );
                    resolveNextTaskLock();
                }
            });
        return startLock
            .then(() =>
                this.debugLog(
                    logger,
                    "Finished waiting in the pending-tasks queue, starting the execution"
                )
            )
            .then(executeTaskAndScheduleNext, executeTaskAndScheduleNext);
    }

    private debugLog(logger: BenchmarkingLogger, ...messages: string[]) {
        const enabledLogger = this.ifEnabled(logger)?.asOneRecord();
        for (const message of messages) {
            enabledLogger?.debug(`${this.schedulerLogsIdentifier}${message}`);
        }
    }

    private ifEnabled(
        logger: BenchmarkingLogger
    ): BenchmarkingLogger | undefined {
        return this.enableSchedulingDebugLogs ? logger : undefined;
    }
}
