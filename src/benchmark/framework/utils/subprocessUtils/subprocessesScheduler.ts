import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { ResolveType } from "../promiseUtils";

export class SubprocessesScheduler {
    constructor(
        private readonly maxActiveSubprocessesNumber: number,
        private readonly enableSchedulingDebugLogs: boolean = false
    ) {}

    private activeSubprocessesNumber: number = 0;
    private readonly pendingSubprocessesLocks: ResolveType<void>[] = [];

    scheduleSubprocess<T>(
        executeSubprocess: () => Promise<T>,
        logger: BenchmarkingLogger
    ): Promise<T> {
        let startLock: Promise<void> = new Promise((resolve, reject) => {
            if (
                this.activeSubprocessesNumber < this.maxActiveSubprocessesNumber
            ) {
                if (this.enableSchedulingDebugLogs) {
                    logger
                        .asOneRecord()
                        .debug("Starting the subprocess execution immediately")
                        .debug(
                            `Increased number of running processes: ${this.activeSubprocessesNumber} --> ${this.activeSubprocessesNumber + 1}`
                        );
                }
                this.activeSubprocessesNumber += 1;
                reject(); // reject is called here to differentiate immediate and pending lock resolutions
            } else {
                logger.debug(
                    `Maximum number of running processes (${this.maxActiveSubprocessesNumber}) is already reached (${this.activeSubprocessesNumber}), waiting for some of them to finish`
                );
                this.pendingSubprocessesLocks.push(resolve);
            }
        });
        const executeSubprocessAndScheduleNext: () => Promise<T> = () =>
            executeSubprocess().finally(() => {
                const resolveNextSubprocessLock =
                    this.pendingSubprocessesLocks.shift();
                if (resolveNextSubprocessLock === undefined) {
                    if (this.enableSchedulingDebugLogs) {
                        logger
                            .asOneRecord()
                            .debug(
                                "Subprocess execution finished, there are no pending executions"
                            )
                            .debug(
                                `Decreased number of running processes: ${this.activeSubprocessesNumber} --> ${this.activeSubprocessesNumber - 1}`
                            );
                    }
                    this.activeSubprocessesNumber -= 1;
                } else {
                    if (this.enableSchedulingDebugLogs) {
                        logger.debug(
                            "Subprocess execution finished, starting the next pending one"
                        );
                    }
                    resolveNextSubprocessLock();
                }
            });
        return startLock
            .then(() =>
                logger.debug(
                    "Finished waiting in the pending-subprocesses queue, starting the execution"
                )
            )
            .then(
                executeSubprocessAndScheduleNext,
                executeSubprocessAndScheduleNext
            );
    }
}
