import { ChatHistory, ChatRole, EstimatedTokens } from "../../chat";
import { ModelParams } from "../../modelParams";

export type ResponseStatus = "SUCCESS" | "FAILURE";

export interface LoggedError {
    typeName: string;
    message: string;
}

export class ParsingError extends Error {
    constructor(message: string, rawParsingData: string) {
        const parsingDataInfo = `\n>> \`${rawParsingData}\``;
        super(`failed to parse log record: ${message}${parsingDataInfo}`);
    }
}

export class LoggerRecord {
    /**
     * Even though this value is in millis, effectively it represents seconds.
     * I.e. this value is always floored to the seconds (`value % 1000 === 0`).
     *
     * The reason is that, unfortunately, the current serialization-deserialization
     * cycle neglects milliseconds.
     */
    readonly timestampMillis: number;

    protected static floorMillisToSeconds(millis: number): number {
        return millis - (millis % 1000);
    }

    constructor(
        timestampMillis: number,
        readonly modelId: string,
        readonly responseStatus: ResponseStatus,
        readonly choices: number,
        readonly estimatedTokens: EstimatedTokens | undefined = undefined,
        readonly error: LoggedError | undefined = undefined
    ) {
        this.timestampMillis =
            LoggerRecord.floorMillisToSeconds(timestampMillis);
    }

    protected static readonly introLinePattern =
        /^\[(.*)\] `(.*)` model: (.*)$/;

    protected static readonly loggedErrorHeader = "! error occurred:";
    protected static readonly loggedErrorPattern =
        /^! error occurred: \[(.*)\] "(.*)"$/;

    protected static readonly choicesPattern = /^- requested choices: (.*)$/;

    protected static readonly requestTokensHeader = "- request's tokens:";
    protected static readonly requestTokensPattern =
        /^- request's tokens: ([0-9]+) = ([0-9]+) \(chat messages\) \+ ([0-9]+) \(max to generate\)$/;

    serializeToString(): string {
        const introInfo = this.buildStatusLine();
        const errorInfo = this.buildErrorInfo();
        const requestInfo = this.buildRequestInfo();
        return `${introInfo}${errorInfo}${requestInfo}`;
    }

    toString(): string {
        return this.serializeToString();
    }

    protected buildStatusLine(): string {
        const timestamp = new Date(this.timestampMillis).toLocaleString();
        return `[${timestamp}] \`${this.modelId}\` model: ${this.responseStatus}\n`;
    }

    protected buildErrorInfo(): string {
        if (this.error === undefined) {
            return "";
        }
        return `${LoggerRecord.loggedErrorHeader} [${this.error.typeName}] "${LoggerRecord.escapeNewlines(this.error.message)}"\n`;
    }

    protected buildRequestInfo(): string {
        const choicesRequested = `- requested choices: ${this.choices}\n`;
        const requestTokens =
            this.estimatedTokens !== undefined
                ? `${LoggerRecord.requestTokensHeader} ${this.estimatedTokensToString()}\n`
                : "";
        return `${choicesRequested}${requestTokens}`;
    }

    private estimatedTokensToString(): string {
        return `${this.estimatedTokens!.maxTokensInTotal} = ${this.estimatedTokens!.messagesTokens} (chat messages) + ${this.estimatedTokens!.maxTokensToGenerate} (max to generate)`;
    }

    protected static escapeNewlines(text: string): string {
        return text.replace("\n", "\\n");
    }

    static deserealizeFromString(rawRecord: string): [LoggerRecord, string] {
        const [rawTimestamp, modelId, rawResponseStatus, afterIntroRawRecord] =
            this.parseFirstLineByRegex(
                this.introLinePattern,
                rawRecord,
                "intro line"
            );
        const timestampMillis = this.parseTimestampMillis(rawTimestamp);
        const responseStatus = this.parseAsType<ResponseStatus>(
            rawResponseStatus,
            "response status"
        );

        const [error, afterLoggedErrorRawRecord] = this.parseOptional(
            this.loggedErrorHeader,
            (text) => this.parseLoggedError(text),
            afterIntroRawRecord
        );

        const [rawChoices, afterChoicesRawRecord] = this.parseFirstLineByRegex(
            this.choicesPattern,
            afterLoggedErrorRawRecord,
            "requested choices"
        );
        const [estimatedTokens, afterTokensRawRecord] = this.parseOptional(
            this.requestTokensHeader,
            (text) => this.parseRequestTokens(text),
            afterChoicesRawRecord
        );

        return [
            new LoggerRecord(
                timestampMillis,
                modelId,
                responseStatus,
                this.parseIntValue(rawChoices, "requested choices"),
                estimatedTokens,
                error
            ),
            afterTokensRawRecord,
        ];
    }

    private static parseLoggedError(text: string): [LoggedError, string] {
        const [errorTypeName, rawErrorMessage, restRawRecord] =
            this.parseFirstLineByRegex(
                this.loggedErrorPattern,
                text,
                "logged error"
            );
        return [
            {
                typeName: errorTypeName,
                message: LoggerRecord.unescapeNewlines(rawErrorMessage),
            },
            restRawRecord,
        ];
    }

    private static parseRequestTokens(text: string): [EstimatedTokens, string] {
        let [
            maxTokensInTotal,
            messagesTokens,
            maxTokensToGenerate,
            restRawRecord,
        ] = this.parseFirstLineByRegex(
            this.requestTokensPattern,
            text,
            "request's tokens header"
        );
        return [
            {
                messagesTokens: this.parseIntValue(
                    messagesTokens,
                    "messages tokens"
                ),
                maxTokensToGenerate: this.parseIntValue(
                    maxTokensToGenerate,
                    "max tokens to generate"
                ),
                maxTokensInTotal: this.parseIntValue(
                    maxTokensInTotal,
                    "max tokens in total"
                ),
            },
            restRawRecord,
        ];
    }

    protected static parseOptional<T>(
        header: string,
        parse: (text: string) => [T, string],
        text: string
    ): [T | undefined, string] {
        if (!text.startsWith(header)) {
            return [undefined, text];
        }
        return parse(text);
    }

    protected static splitByFirstLine(text: string): [string, string] {
        const firstLineEndIndex = text.indexOf("\n");
        if (firstLineEndIndex === -1) {
            throw new ParsingError("line expected", text);
        }
        return [
            text.substring(0, firstLineEndIndex),
            text.substring(firstLineEndIndex + 1),
        ];
    }

    protected static parseAsType<T>(rawValue: string, valueName: string): T {
        const parsedValue = rawValue as T;
        if (parsedValue === null) {
            throw new ParsingError(`invalid ${valueName}`, rawValue);
        }
        return parsedValue;
    }

    protected static parseTimestampMillis(rawTimestamp: string): number {
        try {
            return new Date(rawTimestamp).getTime();
        } catch (e) {
            throw new ParsingError("invalid timestampt", rawTimestamp);
        }
    }

    protected static parseIntValue(
        rawValue: string,
        valueName: string
    ): number {
        try {
            return parseInt(rawValue);
        } catch (e) {
            throw new ParsingError(`invalid ${valueName}`, rawValue);
        }
    }

    protected static parseIntValueOrUndefined(
        rawValue: string,
        valueName: string
    ): number | undefined {
        if (rawValue === "undefined") {
            return undefined;
        }
        return this.parseIntValue(rawValue, valueName);
    }

    protected static parseByRegex(
        pattern: RegExp,
        text: string,
        valueName: string
    ): string[] {
        const match = text.match(pattern);
        if (!match) {
            throw new ParsingError(`invalid ${valueName}`, text);
        }
        return match.slice(1);
    }

    protected static parseFirstLineByRegex(
        pattern: RegExp,
        text: string,
        valueName: string
    ): string[] {
        const [firstLine, restText] = this.splitByFirstLine(text);
        const parsedLine = this.parseByRegex(pattern, firstLine, valueName);
        return [...parsedLine, restText];
    }

    protected static unescapeNewlines(text: string): string {
        return text.replace("\\n", "\n");
    }
}

export class DebugLoggerRecord extends LoggerRecord {
    constructor(
        baseRecord: LoggerRecord,
        readonly chat: ChatHistory | undefined,
        readonly params: ModelParams,
        readonly generatedProofs: string[] | undefined = undefined
    ) {
        super(
            baseRecord.timestampMillis,
            baseRecord.modelId,
            baseRecord.responseStatus,
            baseRecord.choices,
            baseRecord.estimatedTokens,
            baseRecord.error
        );
    }

    protected static readonly subItemIndent = "\t";
    protected static readonly subItemDelimIndented = `${this.subItemIndent}> `;
    protected static readonly jsonStringifyIndent = 2;

    protected static readonly emptyListLine = `${this.subItemIndent}~ empty`;
    protected static readonly emptyListPattern = /^\t~ empty$/;

    protected static readonly chatHeader = "- chat sent:";
    protected static readonly chatHeaderPattern = /^- chat sent:$/;
    protected static readonly chatMessagePattern = /^\t> \[(.*)\]: `(.*)`$/;

    protected static readonly generatedProofsHeader = "- generated proofs:";
    protected static readonly generatedProofsHeaderPattern =
        /^- generated proofs:$/;
    protected static readonly generatedProofPattern = /^\t> `(.*)`$/;

    protected static readonly paramsHeader = "- model's params:";
    protected static readonly paramsHeaderPattern = /^- model's params:$/;

    serializeToString(): string {
        const baseInfo = super.serializeToString();
        const extraInfo = this.buildExtraInfo();
        return `${baseInfo}${extraInfo}`;
    }

    private buildExtraInfo(): string {
        const chatInfo =
            this.chat !== undefined
                ? `${DebugLoggerRecord.chatHeader}\n${this.chatToExtraLogs()}\n`
                : "";
        const generatedProofs =
            this.generatedProofs !== undefined
                ? `${DebugLoggerRecord.generatedProofsHeader}\n${this.proofsToExtraLogs()}\n`
                : "";
        const paramsInfo = `${DebugLoggerRecord.paramsHeader}\n${this.paramsToExtraLogs()}\n`;
        return `${chatInfo}${generatedProofs}${paramsInfo}`;
    }

    private chatToExtraLogs(): string {
        return this.chat!.length === 0
            ? DebugLoggerRecord.emptyListLine
            : this.chat!.map(
                  (message) =>
                      `${DebugLoggerRecord.subItemDelimIndented}[${message.role}]: \`${LoggerRecord.escapeNewlines(message.content)}\``
              ).join("\n");
    }

    private proofsToExtraLogs(): string {
        return this.generatedProofs!.length === 0
            ? DebugLoggerRecord.emptyListLine
            : this.generatedProofs!.map(
                  (proof) =>
                      `${DebugLoggerRecord.subItemDelimIndented}\`${LoggerRecord.escapeNewlines(proof)}\``
              ).join("\n");
    }

    private paramsToExtraLogs(): string {
        return JSON.stringify(
            this.params,
            null,
            DebugLoggerRecord.jsonStringifyIndent
        );
    }

    static deserealizeFromString(
        rawRecord: string
    ): [DebugLoggerRecord, string] {
        const [baseRecord, afterBaseRawRecord] = super.deserealizeFromString(
            rawRecord
        );
        const [chat, afterChatRawRecord] = this.parseOptional(
            this.chatHeader,
            (text) => this.parseChatHistory(text),
            afterBaseRawRecord
        );
        const [generatedProofs, afterProofsRawRecord] = this.parseOptional(
            this.generatedProofsHeader,
            (text) => this.parseGeneratedProofs(text),
            afterChatRawRecord
        );
        const [params, unparsedData] =
            this.parseModelParams(afterProofsRawRecord);

        return [
            new DebugLoggerRecord(baseRecord, chat, params, generatedProofs),
            unparsedData,
        ];
    }

    private static parseChatHistory(text: string): [ChatHistory, string] {
        let [restRawRecord] = this.parseFirstLineByRegex(
            this.chatHeaderPattern,
            text,
            "chat history header"
        );
        const chat: ChatHistory = [];
        if (restRawRecord.startsWith(this.emptyListLine)) {
            return [
                chat,
                this.parseFirstLineByRegex(
                    this.emptyListPattern,
                    restRawRecord,
                    "empty chat history keyword"
                )[0],
            ];
        }
        while (restRawRecord.startsWith(this.subItemDelimIndented)) {
            const [rawRole, rawContent, newRestRawRecord] =
                this.parseFirstLineByRegex(
                    this.chatMessagePattern,
                    restRawRecord,
                    "chat history's message"
                );
            chat.push({
                role: this.parseAsType<ChatRole>(rawRole, "chat role"),
                content: this.unescapeNewlines(rawContent),
            });
            restRawRecord = newRestRawRecord;
        }
        return [chat, restRawRecord];
    }

    private static parseGeneratedProofs(text: string): [string[], string] {
        let [restRawRecord] = this.parseFirstLineByRegex(
            this.generatedProofsHeaderPattern,
            text,
            "generated proofs header"
        );
        const generatedProofs: string[] = [];
        if (restRawRecord.startsWith(this.emptyListLine)) {
            return [
                generatedProofs,
                this.parseFirstLineByRegex(
                    this.emptyListPattern,
                    restRawRecord,
                    "empty generated proofs keyword"
                )[0],
            ];
        }
        while (restRawRecord.startsWith(this.subItemDelimIndented)) {
            const [rawGeneratedProof, newRestRawRecord] =
                this.parseFirstLineByRegex(
                    this.generatedProofPattern,
                    restRawRecord,
                    "generated proof"
                );
            generatedProofs.push(this.unescapeNewlines(rawGeneratedProof));
            restRawRecord = newRestRawRecord;
        }
        return [generatedProofs, restRawRecord];
    }

    private static parseModelParams(text: string): [ModelParams, string] {
        let [restRawRecord] = this.parseFirstLineByRegex(
            this.paramsHeaderPattern,
            text,
            "model's params header"
        );
        const params = this.parseAsType<ModelParams>(
            JSON.parse(restRawRecord),
            "model's params"
        );

        restRawRecord = restRawRecord.slice(
            JSON.stringify(params, null, this.jsonStringifyIndent).length
        );
        if (!restRawRecord.startsWith("\n")) {
            throw new ParsingError(
                `invalid model's params suffix`,
                restRawRecord
            );
        }
        restRawRecord = restRawRecord.slice(1);

        return [params, restRawRecord];
    }
}
