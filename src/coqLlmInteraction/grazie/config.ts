import { parse } from "toml";
import { readFileSync } from "fs";

export interface GrazieConfig {
    gateawayUrl: string;
    chatUrl: string;
}

export class GrazieHolder {
    private static readonly defaultConfigPath = "src/coqLlmInteraction/grazie/grazie_config.toml";

    static create(configPath: string = this.defaultConfigPath): GrazieConfig {
        const config = parse(readFileSync(configPath, "utf-8"));
        const configKeys = {
            gateawayUrl: config['base-url'], 
            chatUrl: config.chat['chat-url']
        };

        if (!configKeys.gateawayUrl || !configKeys.chatUrl) {
            throw new Error("Invalid config file");
        }
    
        return configKeys as GrazieConfig;
    }
}
