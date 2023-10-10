import pino, { LoggerOptions, DestinationStream } from 'pino';
import { window, OutputChannel } from 'vscode';

class VSCodeDestination implements DestinationStream {
    constructor(private channel: OutputChannel) {}

    write(msg: string): void {
        this.channel.appendLine(msg);
    }

    end(msg?: string | (() => void), cb?: () => void): void {
        this.write(msg as string);
        if (cb) { cb(); }
    }

    close(): void {
        this.channel.dispose();
    }
}

const vscodeChannel = window.createOutputChannel('Coqpilot');
const logger = pino({
    formatters: {
        level: (label) => {
            return { level: label };
        },
    },
    level: process.env.LOG_LEVEL || 'info',
    name: process.env.LOGGER_NAME,
    redact: {
        paths: ['email', 'password', 'token'],
    },
    timestamp: pino.stdTimeFunctions.isoTime,
} as LoggerOptions, new VSCodeDestination(vscodeChannel));

export default logger;