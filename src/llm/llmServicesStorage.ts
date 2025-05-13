import { getOrPut } from "../utils/collectionUtils/mapUtils";
import { illegalState } from "../utils/errors/throwErrors";

import { LLMService } from "./llmServices/llmService";
import { LLMServiceIdentifier } from "./llmServices/llmServiceIdentifier";

export class LLMServicesStorage {
    private readonly identifierToServices: Map<
        LLMServiceIdentifier,
        LLMService[]
    > = new Map();
    private readonly customServices: LLMService[] = [];

    registerService(newServiceBuilder: () => LLMService): LLMService {
        const newService = newServiceBuilder();
        const identifier = newService.identifier;

        const servicesOfSameType =
            identifier === undefined
                ? this.customServices
                : getOrPut(
                      this.identifierToServices,
                      identifier,
                      () => [] as LLMService[]
                  );
        for (const existingService of servicesOfSameType) {
            if (newService.isSameInstance(existingService)) {
                newService.dispose();
                illegalState(
                    `Failed to register new service: ${newService.toLogString(false)}; `,
                    `since its instance already exists: ${existingService.toLogString(false)}. `,
                    `Make sure your services of the same type are supposed to be different instances. `,
                    `If it is not the case, use only one of them instead.`
                );
            }
        }
        servicesOfSameType.push(newService as any);

        return newService;
    }

    dispose() {
        for (const services of this.identifierToServices.values()) {
            for (const service of services) {
                service.dispose();
            }
        }
    }

    getServices(identifier: LLMServiceIdentifier | undefined): LLMService[] {
        if (identifier === undefined) {
            return this.customServices;
        } else {
            return this.identifierToServices.get(identifier) ?? [];
        }
    }

    allServices(): LLMService[] {
        return [
            ...Array.from(this.identifierToServices.values()).flat(),
            ...this.customServices,
        ];
    }
}
