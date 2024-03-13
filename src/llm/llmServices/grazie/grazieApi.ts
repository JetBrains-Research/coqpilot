/* eslint-disable @typescript-eslint/naming-convention */
import axios from "axios";
import { ResponseType } from "axios";

import { EventLogger, Severity } from "../../../logging/eventLogger";
import { GrazieModelParams } from "../modelParams";

export type GrazieChatRole = "User" | "System" | "Assistant";
export type GrazieFormattedHistory = { role: GrazieChatRole; text: string }[];

interface GrazieConfig {
    gateawayUrl: string;
    chatUrl: string;
}

export class GrazieApi {
    private readonly config: GrazieConfig;

    constructor(private readonly eventLogger?: EventLogger) {
        this.config = {
            chatUrl: "v5/llm/chat/stream/v3",
            gateawayUrl:
                "https://api.app.stgn.grazie.aws.intellij.net/service/",
        };
    }

    async requestChatCompletion(
        params: GrazieModelParams,
        history: GrazieFormattedHistory
    ): Promise<string> {
        const body = this.createRequestBody(history, params);
        return this.post(this.config.chatUrl, body, params.apiKey);
    }

    private createRequestBody(
        history: GrazieFormattedHistory,
        params: GrazieModelParams
    ): string {
        return JSON.stringify({
            chat: {
                messages: history,
            },
            profile: params.modelName,
        });
    }

    private async post(
        url: string,
        body: string,
        apiToken: string
    ): Promise<string> {
        const headers = this.createHeaders(apiToken);
        headers["Content-Length"] = body.length;
        this.eventLogger?.log(
            "grazie-fetch-started",
            "Completion from Grazie requested",
            {
                url: url,
                body: body,
                headers: headers,
            },
            Severity.DEBUG
        );

        const response = await this.fetchAndProcessEvents(
            this.config.gateawayUrl + url,
            body,
            headers
        );

        return response;
    }

    private createHeaders(token: string): any {
        return {
            Accept: "*/*",
            "Content-Type": "application/json",
            "Grazie-Authenticate-Jwt": token,
            "Grazie-Original-Service-JWT": token,
        };
    }

    private chunkToTokens(chunk: any): string[] {
        const tokens = chunk
            .toString()
            .split("\n")
            .map((line: string) => line.trim())
            .filter((line: string) => line.length > 0);

        const messages: string[] = [];
        tokens.forEach((tokenWrapped: string) => {
            if (tokenWrapped.startsWith("data:")) {
                if (tokenWrapped === "data: end") {
                    return;
                }

                const validJSON = tokenWrapped.substring(
                    tokenWrapped.indexOf("{")
                );
                const messageData = JSON.parse(validJSON);
                messages.push(messageData.current);
            } else {
                throw new Error(
                    "Unexpected chunk: " +
                        tokenWrapped +
                        ". Please report this error."
                );
            }
        });

        return messages;
    }

    private async fetchAndProcessEvents(
        url: string,
        postData: any,
        headers: any
    ): Promise<string> {
        let data: string = "";

        return new Promise<string>(async (resolve, reject) => {
            try {
                const response = await axios.post(url, postData, {
                    headers: headers,
                    responseType: "stream" as ResponseType,
                });

                response.data.on("data", (chunk: any) => {
                    // We receive the data in chunks, which can contain
                    // multiple tokens. We parse them and do append all.
                    const tokens = this.chunkToTokens(chunk);
                    data += tokens.join("");
                });

                // Handle end of data stream
                response.data.on("end", function () {
                    resolve(data);
                });

                // On error, reject the Promise
                response.data.on("error", function (err: any) {
                    console.error("Stream error:", err);
                    reject(err);
                });
            } catch (error) {
                console.error("Error in axios request: ", error);
                reject(error);
            }
        });
    }
}
