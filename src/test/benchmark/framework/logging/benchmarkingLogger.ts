import { LogColor, colorize } from "./colorLogging";

export enum SeverityLevel {
    ERROR = 0,
    INFO = 1,
    DEBUG = 2,
}

export abstract class BenchmarkingLogger {
    constructor(
        protected loggerSeverity: SeverityLevel,
        protected recordIdentifier: string = "",
        protected lineEnd: string = "\n"
    ) {}

    setLoggerSeverity(severity: SeverityLevel) {
        this.loggerSeverity = severity;
    }

    abstract createChildLoggerWithIdentifier(
        recordIdentifier: string
    ): BenchmarkingLogger;

    protected abstract log(
        severity: SeverityLevel,
        message: string,
        color: LogColor | undefined,
        lineEnd: string,
        recordIdentifier: string
    ): void;

    error(
        message: string,
        color: LogColor | undefined = "red",
        lineEnd: string = this.lineEnd,
        recordIdentifier: string = this.recordIdentifier
    ) {
        this.log(
            SeverityLevel.ERROR,
            message,
            color,
            recordIdentifier,
            lineEnd
        );
    }

    info(
        message: string,
        color: LogColor | undefined = undefined,
        lineEnd: string = this.lineEnd,
        recordIdentifier: string = this.recordIdentifier
    ) {
        this.log(SeverityLevel.INFO, message, color, recordIdentifier, lineEnd);
    }

    debug(
        message: string,
        color: LogColor | undefined = "gray",
        lineEnd: string = this.lineEnd,
        recordIdentifier: string = this.recordIdentifier
    ) {
        this.log(
            SeverityLevel.DEBUG,
            message,
            color,
            recordIdentifier,
            lineEnd
        );
    }

    separatorLine(
        suffix: string = "",
        severity: SeverityLevel = SeverityLevel.INFO,
        color: LogColor | undefined = undefined
    ) {
        this.log(severity, `----------------------------`, color, "", suffix);
    }

    buildLogs(separator = "\n"): AppendLogsBuilder {
        return new AppendLogsBuilder(this, separator);
    }

    asOneRecord(): AsOneRecordLogsBuilder {
        return new AsOneRecordLogsBuilder(this, this.lineEnd);
    }
}

export class AsOneRecordLogsBuilder {
    constructor(
        private readonly logger: BenchmarkingLogger,
        private readonly lineEnd: string
    ) {}

    private firstMessageLogged = false;

    private logImpl(
        callLogger: (
            message: string,
            color: LogColor | undefined,
            lineEnd: string,
            recordIdentifier?: string
        ) => void,
        message: string,
        color: LogColor | undefined,
        lineEnd: string
    ): AsOneRecordLogsBuilder {
        if (this.firstMessageLogged) {
            callLogger(message, color, lineEnd, "");
        } else {
            callLogger(message, color, lineEnd);
            this.firstMessageLogged = true;
        }
        return this;
    }

    error(
        message: string,
        color: LogColor | undefined = "red",
        lineEnd: string = this.lineEnd
    ): AsOneRecordLogsBuilder {
        return this.logImpl(
            this.logger.error.bind(this.logger),
            message,
            color,
            lineEnd
        );
    }

    info(
        message: string,
        color: LogColor | undefined = undefined,
        lineEnd: string = this.lineEnd
    ): AsOneRecordLogsBuilder {
        return this.logImpl(
            this.logger.info.bind(this.logger),
            message,
            color,
            lineEnd
        );
    }

    debug(
        message: string,
        color: LogColor | undefined = "gray",
        lineEnd: string = this.lineEnd
    ): AsOneRecordLogsBuilder {
        return this.logImpl(
            this.logger.debug.bind(this.logger),
            message,
            color,
            lineEnd
        );
    }
}

export class AppendLogsBuilder {
    constructor(
        private readonly logger: BenchmarkingLogger,
        private readonly separator: string
    ) {}

    private buffer: [string, LogColor | undefined][] = [];

    append(message: string, color?: LogColor): AppendLogsBuilder {
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

    private checkAtLeastOneColorIsOverriden(commonColor?: LogColor): boolean {
        return (
            commonColor !== undefined ||
            this.buffer.filter(
                ([_, messageColor]) => messageColor !== undefined
            ).length > 0
        );
    }

    private logImpl(
        callLogger: (message: string, color?: LogColor | undefined) => void,
        commonColor?: LogColor
    ) {
        if (this.checkAtLeastOneColorIsOverriden(commonColor)) {
            callLogger(this.joinLogs(commonColor), undefined);
        } else {
            callLogger(this.joinLogs(commonColor));
        }
    }

    error(color?: LogColor) {
        this.logImpl(this.logger.error.bind(this.logger), color);
    }

    info(color?: LogColor) {
        this.logImpl(this.logger.info.bind(this.logger), color);
    }

    debug(color?: LogColor) {
        this.logImpl(this.logger.debug.bind(this.logger), color);
    }
}

export class BenchmarkingLoggerImpl extends BenchmarkingLogger {
    createChildLoggerWithIdentifier(
        recordIdentifier: string
    ): BenchmarkingLogger {
        return new BenchmarkingLoggerImpl(
            this.loggerSeverity,
            recordIdentifier
        );
    }

    protected log(severity: SeverityLevel, message: string, color?: LogColor) {
        if (this.loggerSeverity < severity) {
            return;
        }
        this.print(this.recordIdentifier);
        if (color === undefined) {
            this.print(message);
        } else {
            this.print(colorize(message, color));
        }
    }

    private print(message: string) {
        console.log(message);
    }
}
