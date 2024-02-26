import pino, { LoggerOptions, DestinationStream } from "pino";
import { window, OutputChannel } from "vscode";
import { Severity, EventLogger, ALL_EVENTS } from "../logging/eventLogger";

class VSCodeLogWriter {
    private readonly outputStream = new VSCodeOutputChannelDestinationStream(
        window.createOutputChannel("CoqPilot Events")
    );
    private readonly outputStreamWriter = pino(
        {
            formatters: {
                level: (label) => {
                    return { level: label };
                },
            },
            level: process.env.LOG_LEVEL || "info",
            redact: {
                paths: ["*.password", "*.token", "*.apiKey"],
                censor: "***censored***",
            },
            timestamp: pino.stdTimeFunctions.isoTime,
        } as LoggerOptions,
        this.outputStream
    );

    constructor(eventLogger: EventLogger, logLevel: Severity = Severity.INFO) {
        eventLogger.subscribe(ALL_EVENTS, Severity.INFO, (message, data) => {
            this.outputStreamWriter.info({
                message,
                data,
            });
        });
        if (logLevel === Severity.DEBUG) {
            eventLogger.subscribe(
                ALL_EVENTS,
                Severity.DEBUG,
                (message, data) => {
                    this.outputStreamWriter.info({
                        message,
                        data,
                    });
                }
            );
        }
    }

    dispose(): void {
        this.outputStreamWriter.flush();
        this.outputStream.close();
    }
}

class VSCodeOutputChannelDestinationStream implements DestinationStream {
    constructor(private channel: OutputChannel) {}

    write(msg: string): void {
        this.channel.appendLine(msg);
    }

    end(msg?: string | (() => void), cb?: () => void): void {
        this.write(msg as string);
        if (cb) {
            cb();
        }
    }

    close(): void {
        this.channel.dispose();
    }
}

export default VSCodeLogWriter;
