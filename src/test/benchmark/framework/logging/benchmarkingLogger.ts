import { LogColor, colorize } from "./colorLogging";

export enum SeverityLevel {
    ERROR = 0,
    INFO = 1,
    DEBUG = 2,
}

export abstract class BenchmarkingLogger {
    constructor(
        protected loggerSeverity: SeverityLevel,
        protected logsIdentifier: string = ""
    ) {}

    setLoggerSeverity(severity: SeverityLevel) {
        this.loggerSeverity = severity;
    }

    abstract createChildLoggerWithIdentifier(
        identifier: string
    ): BenchmarkingLogger;

    protected abstract log(
        severity: SeverityLevel,
        message: string,
        color?: LogColor
    ): void;

    error(message: string, color: LogColor | undefined = "red") {
        this.log(SeverityLevel.ERROR, message, color);
    }

    info(message: string, color: LogColor | undefined = undefined) {
        this.log(SeverityLevel.INFO, message, color);
    }

    debug(message: string, color: LogColor | undefined = "gray") {
        this.log(SeverityLevel.DEBUG, message, color);
    }

    separatorLine(
        suffix: string = "",
        severity: SeverityLevel = SeverityLevel.INFO
    ) {
        this.log(severity, `----------------------------${suffix}`);
    }

    buildLogs(separator = "\n"): LogsBuilder {
        return new LogsBuilder(this, separator);
    }
}

export class LogsBuilder {
    constructor(
        private readonly logger: BenchmarkingLogger,
        private readonly separator: string
    ) {}

    private buffer: [string, LogColor | undefined][] = [];

    append(message: string, color?: LogColor): LogsBuilder {
        this.buffer.push([message, color]);
        return this;
    }

    private joinLogs(commonColor: LogColor | undefined): string {
        if (commonColor === undefined) {
            return this.buffer
                .map(([message, messageColor]) =>
                    colorize(message, messageColor)
                )
                .join(this.separator);
        } else {
            return this.buffer
                .map(([message, _]) => colorize(message, commonColor))
                .join(this.separator);
        }
    }

    error(color?: LogColor) {
        this.logger.error(this.joinLogs(color), undefined);
    }

    info(color?: LogColor) {
        this.logger.info(this.joinLogs(color), undefined);
    }

    debug(color?: LogColor) {
        this.logger.debug(this.joinLogs(color), undefined);
    }
}

export class BenchmarkingLoggerImpl extends BenchmarkingLogger {
    createChildLoggerWithIdentifier(identifier: string): BenchmarkingLogger {
        return new BenchmarkingLoggerImpl(this.loggerSeverity, identifier);
    }

    protected log(severity: SeverityLevel, message: string, color?: LogColor) {
        if (this.loggerSeverity < severity) {
            return;
        }
        const messageWithIdentifier = `${this.logsIdentifier} ${message}`;
        if (color === undefined) {
            this.print(messageWithIdentifier);
        } else {
            this.print(colorize(messageWithIdentifier, color));
        }
    }

    private print(message: string) {
        console.log(message);
    }
}
