export interface GrazieConfig {
    gateawayUrl: string;
    chatUrl: string;
}

export class GrazieHolder {
    static create(): GrazieConfig {
        return {
            chatUrl: "v5/llm/chat/stream/v3",
            gateawayUrl:
                "https://api.app.stgn.grazie.aws.intellij.net/service/",
        };
    }
}
