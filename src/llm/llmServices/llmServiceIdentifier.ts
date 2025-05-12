import { ExternalServiceParams } from "./abstractExternalService/abstractExternalServiceParams";
import { DeepSeekService } from "./deepSeek/deepSeekService";
import { GrazieService } from "./grazie/grazieService";
import { LLMServiceParams } from "./llmServiceParams";
import { LMStudioService } from "./lmStudio/lmStudioService";
import { OpenAiService } from "./openai/openAiService";
import { PredefinedProofsService } from "./predefinedProofs/predefinedProofsService";
import { RangoService } from "./rango/rangoService";
import { LLMServiceCustomizationParams } from "./utils/llmServiceControlParams";

export enum LLMServiceIdentifier {
    PREDEFINED_PROOFS = "Predefined Proofs",
    OPENAI = "Open AI",
    GRAZIE = "Grazie",
    LMSTUDIO = "LM Studio",
    DEEPSEEK = "DeepSeek",
    RANGO = "Rango",
}

export type CorrespondingLLMServiceType<T extends LLMServiceIdentifier> =
    T extends LLMServiceIdentifier.PREDEFINED_PROOFS
        ? PredefinedProofsService
        : T extends LLMServiceIdentifier.OPENAI
          ? OpenAiService
          : T extends LLMServiceIdentifier.GRAZIE
            ? GrazieService
            : T extends LLMServiceIdentifier.LMSTUDIO
              ? LMStudioService
              : T extends LLMServiceIdentifier.DEEPSEEK
                ? DeepSeekService
                : T extends LLMServiceIdentifier.RANGO
                  ? RangoService
                  : never;

export type CorrespondingServiceParams<T extends LLMServiceIdentifier> =
    T extends LLMServiceIdentifier.PREDEFINED_PROOFS
        ? LLMServiceParams
        : T extends LLMServiceIdentifier.OPENAI
          ? LLMServiceParams
          : T extends LLMServiceIdentifier.GRAZIE
            ? LLMServiceParams
            : T extends LLMServiceIdentifier.LMSTUDIO
              ? LLMServiceParams
              : T extends LLMServiceIdentifier.DEEPSEEK
                ? LLMServiceParams
                : T extends LLMServiceIdentifier.RANGO
                  ? ExternalServiceParams
                  : never;

export type CorrespondingInputServiceParams<T extends LLMServiceIdentifier> =
    LLMServiceCustomizationParams<CorrespondingServiceParams<T>>;

export type LLMServiceStringIdentifier =
    | "predefined"
    | "openai"
    | "grazie"
    | "lmstudio"
    | "deepseek"
    | "rango";

export type CorrespondingIdentifier<T extends LLMServiceStringIdentifier> =
    T extends "predefined"
        ? LLMServiceIdentifier.PREDEFINED_PROOFS
        : T extends "openai"
          ? LLMServiceIdentifier.OPENAI
          : T extends "grazie"
            ? LLMServiceIdentifier.GRAZIE
            : T extends "lmstudio"
              ? LLMServiceIdentifier.LMSTUDIO
              : T extends "deepseek"
                ? LLMServiceIdentifier.DEEPSEEK
                : T extends "rango"
                  ? LLMServiceIdentifier.RANGO
                  : never;

export function toEnumIdentifier(
    stringIdentifier: LLMServiceStringIdentifier
): LLMServiceIdentifier {
    switch (stringIdentifier) {
        case "predefined":
            return LLMServiceIdentifier.PREDEFINED_PROOFS;
        case "openai":
            return LLMServiceIdentifier.OPENAI;
        case "grazie":
            return LLMServiceIdentifier.GRAZIE;
        case "lmstudio":
            return LLMServiceIdentifier.LMSTUDIO;
        case "deepseek":
            return LLMServiceIdentifier.DEEPSEEK;
        case "rango":
            return LLMServiceIdentifier.RANGO;
    }
}
