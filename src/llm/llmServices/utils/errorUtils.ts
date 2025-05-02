import { ConfigurationError } from "../../llmServiceErrors";

export function throwConfigurationError(...message: string[]): never {
    throw new ConfigurationError(message.join(""));
}
