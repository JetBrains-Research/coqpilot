import { zip } from "../utils/collectionUtils/listUtils";
import { illegalState } from "../utils/errors/throwErrors";

import { DeepSeekService } from "./llmServices/deepSeek/deepSeekService";
import { GrazieService } from "./llmServices/grazie/grazieService";
import { LLMService } from "./llmServices/llmService";
import {
    CorrespondingLLMServiceType,
    LLMServiceIdentifier,
} from "./llmServices/llmServiceIdentifier";
import { LMStudioService } from "./llmServices/lmStudio/lmStudioService";
import { ModelParams } from "./llmServices/modelParams";
import { OpenAiService } from "./llmServices/openai/openAiService";
import { PredefinedProofsService } from "./llmServices/predefinedProofs/predefinedProofsService";
import { RangoService } from "./llmServices/rango/rangoService";
import { UserModelParams } from "./userModelParams";

type CorrespondingLLMServiceTypeFromKey<
    T extends LLMServiceIdentifier | undefined,
> = T extends undefined
    ? LLMService<any, any>
    : T extends LLMServiceIdentifier
      ? CorrespondingLLMServiceType<T>
      : never;

export class LLMServicesStorage {
    private readonly identifierToServices: Map<
        LLMServiceIdentifier,
        CorrespondingLLMServiceType<LLMServiceIdentifier>[]
    > = new Map();
    private readonly customServices: LLMService<any, any>[] = [];

    getServices<K extends LLMServiceIdentifier | undefined>(
        identifier: K
    ): CorrespondingLLMServiceTypeFromKey<K>[] {
        if (identifier === undefined) {
            return this
                .customServices as CorrespondingLLMServiceTypeFromKey<K>[];
        } else {
            return (this.identifierToServices.get(identifier) ??
                []) as CorrespondingLLMServiceTypeFromKey<K>[];
        }
    }

    registerService<
        T extends CorrespondingLLMServiceTypeFromKey<
            LLMServiceIdentifier | undefined
        >,
    >(newServiceBuilder: () => T): T {
        const newService = newServiceBuilder();
        const identifier = newService.identifier;

        const servicesOfSameType =
            identifier === undefined
                ? this.customServices
                : (this.identifierToServices.get(identifier) ?? []);
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

    allServices(): LLMService<any, any>[] {
        return [
            ...Array.from(this.identifierToServices.values()).flat(),
            ...this.customServices,
        ];
    }
}

export interface LLMServices {
    predefinedProofsService: PredefinedProofsService;
    openAiService: OpenAiService;
    grazieService: GrazieService;
    lmStudioService: LMStudioService;
    deepSeekService: DeepSeekService;
    rangoService: RangoService;
}

export function disposeServices(llmServices: LLMServices) {
    asLLMServices(llmServices).forEach((service) => service.dispose());
}

export function asLLMServices(
    llmServices: LLMServices
): LLMService<UserModelParams, ModelParams>[] {
    return [
        llmServices.predefinedProofsService,
        llmServices.openAiService,
        llmServices.grazieService,
        llmServices.lmStudioService,
        llmServices.deepSeekService,
        llmServices.rangoService,
    ];
}

export function asLLMServicesWithItems<T>(
    llmServices: LLMServices,
    ...items: T[]
): [LLMService<UserModelParams, ModelParams>, T][] {
    return zip(asLLMServices(llmServices), items);
}

export function switchByLLMServiceType<T>(
    llmService: LLMService<any, any>,
    onPredefinedProofsService: () => T,
    onOpenAiService: () => T,
    onGrazieService: () => T,
    onLMStudioService: () => T,
    onDeepSeekService: () => T,
    onRangoService: () => T
): T {
    if (llmService instanceof PredefinedProofsService) {
        return onPredefinedProofsService();
    } else if (llmService instanceof OpenAiService) {
        return onOpenAiService();
    } else if (llmService instanceof GrazieService) {
        return onGrazieService();
    } else if (llmService instanceof LMStudioService) {
        return onLMStudioService();
    } else if (llmService instanceof DeepSeekService) {
        return onDeepSeekService();
    } else if (llmService instanceof RangoService) {
        return onRangoService();
    } else {
        illegalState(`switch by unknown \`LLMService\`: "${llmService.name}"`);
    }
}
