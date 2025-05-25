import { ConfigurationError } from "../../proofProviderErrors";

export function throwConfigurationError(...message: string[]): never {
    throw new ConfigurationError(message.join(""));
}
