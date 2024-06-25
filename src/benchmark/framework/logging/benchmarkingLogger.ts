import { stringifyAnyValue } from "../../../utils/printers";
import {
    appendToFile,
    createFileWithParentDirectories,
} from "../utils/fsUtils";

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
            lineEnd,
            recordIdentifier
        );
    }

    info(
        message: string,
        color: LogColor | undefined = undefined,
        lineEnd: string = this.lineEnd,
        recordIdentifier: string = this.recordIdentifier
    ) {
        this.log(SeverityLevel.INFO, message, color, lineEnd, recordIdentifier);
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
            lineEnd,
            recordIdentifier
        );
    }

    separatorLine(
        suffix: string = "",
        severity: SeverityLevel = SeverityLevel.INFO,
        color: LogColor | undefined = undefined
    ) {
        this.log(severity, `----------------------------`, color, "", suffix);
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

export interface LogsFile {
    resolvedFilePath: string;
    clearOnStart: boolean;
}

export class BenchmarkingLoggerImpl extends BenchmarkingLogger {
    constructor(
        loggerSeverity: SeverityLevel,
        readonly logsFile: LogsFile | undefined,
        recordIdentifier: string = "",
        lineEnd: string = "\n"
    ) {
        super(loggerSeverity, recordIdentifier, lineEnd);
        if (!this.recordIdentifier.startsWith("\n")) {
            this.recordIdentifier = `\n${this.recordIdentifier}`;
        }
        if (this.logsFile !== undefined && this.logsFile.clearOnStart) {
            createFileWithParentDirectories(
                "clear",
                this.logsFile.resolvedFilePath
            );
        }
    }

    createChildLoggerWithIdentifier(
        recordIdentifier: string
    ): BenchmarkingLogger {
        return new BenchmarkingLoggerImpl(
            this.loggerSeverity,
            this.logsFile === undefined
                ? undefined
                : {
                      ...this.logsFile,
                      clearOnStart: false,
                  },
            `${this.buildChildRecordIdentifier(recordIdentifier)}`,
            this.lineEnd
        );
    }

    private buildChildRecordIdentifier(recordIdentifier: string): string {
        return [this.recordIdentifier, recordIdentifier]
            .filter((identifier) => identifier !== "")
            .join(this.lineEnd);
    }

    protected log(
        severity: SeverityLevel,
        message: string,
        color: LogColor | undefined,
        lineEnd: string,
        recordIdentifier: string
    ) {
        if (this.loggerSeverity < severity) {
            return;
        }
        // This condition is needed, for example, for `asOneRecord()`.
        if (recordIdentifier !== "") {
            this.print(recordIdentifier, lineEnd);
        }
        if (color === undefined || this.logsFile !== undefined) {
            // Typically, colors are not supported in files.
            this.print(message, lineEnd);
        } else {
            this.print(colorize(message, color), lineEnd);
        }
    }

    private print(message: string, lineEnd: string) {
        const messageWithLineEnd = `${message}${lineEnd}`;
        if (this.logsFile === undefined) {
            // TODO: does not work in tests => will be fixed after moving out from tests
            // for now, `console.error` can be used (but `lineEnd`-s won't be supported then)
            console.error(message);
            // process.stderr.write(messageWithLineEnd);
        } else {
            appendToFile(
                messageWithLineEnd,
                this.logsFile.resolvedFilePath,
                (e) =>
                    console.error(
                        `Failed to append message to logs file "${this.logsFile}": "${message}"\nCause: ${stringifyAnyValue(e)}`
                    )
            );
        }
    }
}
