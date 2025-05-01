import { BenchmarkingLogger } from "./benchmarkingLogger";

export type SeverityLevelName = "error" | "info" | "warning";

export function logBySeverityLevelName(
    logger: BenchmarkingLogger,
    severity: SeverityLevelName,
    message: string
) {
    switch (severity) {
        case "error":
            logger.error(message);
            return;
        case "info":
            logger.info(message);
            return;
        case "warning":
            logger.info(message, "yellow");
            return;
    }
}
