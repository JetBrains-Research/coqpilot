import { AjvMode, buildAjv } from "../../../../utils/ajvErrorsHandling";
import {
    JsonSpacing,
    stringifyAnyValue,
    toJsonString,
} from "../../../../utils/printers";
import {
    ChatHistory,
    ChatRole,
    EstimatedTokens,
} from "../../commonStructures/chat";
import { GenerationTokens } from "../../commonStructures/generationTokens";
import { ModelParams, modelParamsSchema } from "../../modelParams";

export type ResponseStatus = "SUCCESS" | "FAILURE";

export interface LoggedError {
    typeName: string;
    message: string;
}

export class GenerationsLogsParsingError extends Error {
    constructor(message: string, rawParsingData: string) {
        const parsingDataInfo = `\n>> \`${rawParsingData}\``;
        super(`failed to parse log record: ${message}${parsingDataInfo}`);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ParsingError";
    }
}

// TODO: support `proofGenerationType` if ever needed
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
        readonly requestTokens: EstimatedTokens | undefined = undefined,
        readonly generationTokens: GenerationTokens | undefined = undefined,
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

    protected static readonly generationTokensHeader =
        "- successful generation tokens:";
    protected static readonly generationTokensPattern =
        /^- successful generation tokens: ([0-9]+) = ([0-9]+) \(prompt\) \+ ([0-9]+) \(generated answer\)$/;

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
        const timestamp = new Date(this.timestampMillis).toISOString();
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
            this.requestTokens !== undefined
                ? `${LoggerRecord.requestTokensHeader} ${this.requestTokensToString()}\n`
                : "";
        const generationTokens =
            this.generationTokens !== undefined
                ? `${LoggerRecord.generationTokensHeader} ${this.generationTokensToString()}\n`
                : "";
        return `${choicesRequested}${requestTokens}${generationTokens}`;
    }

    private requestTokensToString(): string {
        const tokens = this.requestTokens!;
        return `${tokens.maxTokensInTotal} = ${tokens.messagesTokens} (chat messages) + ${tokens.maxTokensToGenerate} (max to generate)`;
    }

    private generationTokensToString(): string {
        const tokens = this.generationTokens!;
        return `${tokens.tokensSpentInTotal} = ${tokens.promptTokens} (prompt) + ${tokens.generatedTokens} (generated answer)`;
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
        const responseStatus = this.parseAsType<string, ResponseStatus>(
            rawResponseStatus,
            "response status",
            (rawValue) => rawValue === "SUCCESS" || rawValue === "FAILURE"
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
        const choices = this.parseIntValue(rawChoices, "requested choices");

        const [requestTokens, afterRequestTokensRawRecord] = this.parseOptional(
            this.requestTokensHeader,
            (text) => this.parseRequestTokens(text),
            afterChoicesRawRecord
        );
        const [generationTokens, afterGenerationTokensRawRecord] =
            this.parseOptional(
                this.generationTokensHeader,
                (text) => this.parseGenerationTokens(text),
                afterRequestTokensRawRecord
            );

        return [
            new LoggerRecord(
                timestampMillis,
                modelId,
                responseStatus,
                choices,
                requestTokens,
                generationTokens,
                error
            ),
            afterGenerationTokensRawRecord,
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

    private static parseGenerationTokens(
        text: string
    ): [GenerationTokens, string] {
        let [tokensSpentInTotal, promptTokens, generatedTokens, restRawRecord] =
            this.parseFirstLineByRegex(
                this.generationTokensPattern,
                text,
                "generation tokens header"
            );
        return [
            {
                promptTokens: this.parseIntValue(promptTokens, "prompt tokens"),
                generatedTokens: this.parseIntValue(
                    generatedTokens,
                    "generated answer tokens"
                ),
                tokensSpentInTotal: this.parseIntValue(
                    tokensSpentInTotal,
                    "tokens spent in total"
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
            throw new GenerationsLogsParsingError("line expected", text);
        }
        return [
            text.substring(0, firstLineEndIndex),
            text.substring(firstLineEndIndex + 1),
        ];
    }

    protected static parseAsType<RawType, ParsedType extends RawType>(
        rawValue: RawType,
        valueName: string,
        checkType: (rawValue: RawType) => rawValue is ParsedType
    ): ParsedType {
        if (!checkType(rawValue)) {
            throw new GenerationsLogsParsingError(
                `invalid ${valueName}`,
                stringifyAnyValue(rawValue)
            );
        }
        return rawValue;
    }

    protected static parseTimestampMillis(rawTimestamp: string): number {
        try {
            return new Date(rawTimestamp).getTime();
        } catch (e) {
            throw new GenerationsLogsParsingError(
                "invalid timestampt",
                rawTimestamp
            );
        }
    }

    protected static parseIntValue(
        rawValue: string,
        valueName: string
    ): number {
        try {
            return parseInt(rawValue);
        } catch (e) {
            throw new GenerationsLogsParsingError(
                `invalid ${valueName}`,
                rawValue
            );
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
            throw new GenerationsLogsParsingError(`invalid ${valueName}`, text);
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
        readonly contextTheorems: string[] | undefined,
        readonly chat: ChatHistory | undefined,
        readonly params: ModelParams,
        readonly generatedProofs: string[] | undefined = undefined
    ) {
        super(
            baseRecord.timestampMillis,
            baseRecord.modelId,
            baseRecord.responseStatus,
            baseRecord.choices,
            baseRecord.requestTokens,
            baseRecord.generationTokens,
            baseRecord.error
        );
    }

    protected static readonly subItemIndent = "\t";
    protected static readonly subItemDelimIndented = `${this.subItemIndent}> `;
    protected static readonly jsonStringifyIndent =
        JsonSpacing.DEFAULT_FORMATTED;

    protected static readonly emptyListLine = `${this.subItemIndent}~ empty`;
    protected static readonly emptyListPattern = /^\t~ empty$/;

    protected static readonly contextTheoremsHeader = "- context theorems:";
    protected static readonly contextTheoremsHeaderPattern =
        /^- context theorems:$/;
    protected static readonly contextTheoremsPattern = /^\t> "(.*)"$/;

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
        const contextTheorems =
            this.contextTheorems !== undefined
                ? `${DebugLoggerRecord.contextTheoremsHeader}\n${this.contextTheoremsToExtraLogs()}\n`
                : "";
        const chatInfo =
            this.chat !== undefined
                ? `${DebugLoggerRecord.chatHeader}\n${this.chatToExtraLogs()}\n`
                : "";
        const generatedProofs =
            this.generatedProofs !== undefined
                ? `${DebugLoggerRecord.generatedProofsHeader}\n${this.proofsToExtraLogs()}\n`
                : "";
        const paramsInfo = `${DebugLoggerRecord.paramsHeader}\n${this.paramsToExtraLogs()}\n`;
        return `${contextTheorems}${chatInfo}${generatedProofs}${paramsInfo}`;
    }

    private contextTheoremsToExtraLogs(): string {
        return this.contextTheorems!.length === 0
            ? DebugLoggerRecord.emptyListLine
            : this.contextTheorems!.map(
                  (theoremName) =>
                      `${DebugLoggerRecord.subItemDelimIndented}"${LoggerRecord.escapeNewlines(theoremName)}"`
              ).join("\n");
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
        return toJsonString(this.params, DebugLoggerRecord.jsonStringifyIndent);
    }

    static deserealizeFromString(
        rawRecord: string
    ): [DebugLoggerRecord, string] {
        const [baseRecord, afterBaseRawRecord] = super.deserealizeFromString(
            rawRecord
        );
        const [contextTheorems, afterTheoremsRawRecord] = this.parseOptional(
            this.contextTheoremsHeader,
            (text) => this.parseContextTheorems(text),
            afterBaseRawRecord
        );
        const [chat, afterChatRawRecord] = this.parseOptional(
            this.chatHeader,
            (text) => this.parseChatHistory(text),
            afterTheoremsRawRecord
        );
        const [generatedProofs, afterProofsRawRecord] = this.parseOptional(
            this.generatedProofsHeader,
            (text) => this.parseGeneratedProofs(text),
            afterChatRawRecord
        );
        const [params, unparsedData] =
            this.parseModelParams(afterProofsRawRecord);

        return [
            new DebugLoggerRecord(
                baseRecord,
                contextTheorems,
                chat,
                params,
                generatedProofs
            ),
            unparsedData,
        ];
    }

    private static parseContextTheorems(text: string): [string[], string] {
        let [restRawRecord] = this.parseFirstLineByRegex(
            this.contextTheoremsHeaderPattern,
            text,
            "context theorems header"
        );
        const contextTheorems: string[] = [];
        if (restRawRecord.startsWith(this.emptyListLine)) {
            return [
                contextTheorems,
                this.parseFirstLineByRegex(
                    this.emptyListPattern,
                    restRawRecord,
                    "empty context theorems keyword"
                )[0],
            ];
        }
        while (restRawRecord.startsWith(this.subItemDelimIndented)) {
            const [rawContextTheorem, newRestRawRecord] =
                this.parseFirstLineByRegex(
                    this.contextTheoremsPattern,
                    restRawRecord,
                    "context theorem"
                );
            contextTheorems.push(this.unescapeNewlines(rawContextTheorem));
            restRawRecord = newRestRawRecord;
        }
        return [contextTheorems, restRawRecord];
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
                role: this.parseAsType<string, ChatRole>(
                    rawRole,
                    "chat role",
                    (rawValue) =>
                        rawValue === "system" ||
                        rawValue === "user" ||
                        rawValue === "assistant"
                ),
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

    private static modelParamsResolver = buildAjv(
        AjvMode.RETURN_AFTER_FIRST_ERROR
    ).compile({ ...modelParamsSchema, additionalProperties: true });

    private static parseModelParams(text: string): [ModelParams, string] {
        let [restRawRecord] = this.parseFirstLineByRegex(
            this.paramsHeaderPattern,
            text,
            "model's params header"
        );
        const params = this.parseAsType<any, ModelParams>(
            JSON.parse(restRawRecord),
            "model's params",
            this.modelParamsResolver
        );

        restRawRecord = restRawRecord.slice(
            toJsonString(params, this.jsonStringifyIndent).length
        );
        if (!restRawRecord.startsWith("\n")) {
            throw new GenerationsLogsParsingError(
                `invalid model's params suffix`,
                restRawRecord
            );
        }
        restRawRecord = restRawRecord.slice(1);

        return [params, restRawRecord];
    }
}
