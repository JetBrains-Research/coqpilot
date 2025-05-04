import { ExternalServiceParams } from "../../../../llm/llmServices/abstractExternalService/abstractExternalServiceParams";
import { LLMServiceParams } from "../../../../llm/llmServices/llmServiceParams";

import { InputBenchmarkingModelParams } from "../inputParameters/inputBenchmarkingModelParams";

export enum LLMServiceIdentifier {
    PREDEFINED_PROOFS = "Predefined Proofs",
    OPENAI = "Open AI",
    GRAZIE = "Grazie",
    LMSTUDIO = "LM Studio",
    DEEPSEEK = "DeepSeek",
    RANGO = "Rango",
}

export type LLMServiceStringIdentifier =
    | "predefined"
    | "openai"
    | "grazie"
    | "lmstudio"
    | "deepseek"
    | "rango";

export type CorrespondingServiceParams<T extends LLMServiceStringIdentifier> =
    T extends "predefined"
        ? LLMServiceParams
        : T extends "openai"
          ? LLMServiceParams
          : T extends "grazie"
            ? LLMServiceParams
            : T extends "lmstudio"
              ? LLMServiceParams
              : T extends "deepseek"
                ? LLMServiceParams
                : T extends "rango"
                  ? ExternalServiceParams
                  : never;

export type CorrespondingInputServiceParams<
    T extends LLMServiceStringIdentifier,
> = Omit<CorrespondingServiceParams<T>, "eventLogger" | "errorsHandlingMode">;

export type CorrespondingInputParams<T extends LLMServiceStringIdentifier> =
    T extends "predefined"
        ? InputBenchmarkingModelParams.PredefinedProofsParams
        : T extends "openai"
          ? InputBenchmarkingModelParams.OpenAiParams
          : T extends "grazie"
            ? InputBenchmarkingModelParams.GrazieParams
            : T extends "lmstudio"
              ? InputBenchmarkingModelParams.LMStudioParams
              : T extends "deepseek"
                ? InputBenchmarkingModelParams.DeepSeekParams
                : T extends "rango"
                  ? InputBenchmarkingModelParams.RangoParams
                  : never;

// Legacy ?
// function toEnumIdentifier(
//     llmServiceStringIdentifier: LLMServiceStringIdentifier
// ): LLMServiceIdentifier {
//     switch (llmServiceStringIdentifier) {
//         case "predefined":
//             return LLMServiceIdentifier.PREDEFINED_PROOFS;
//         case "openai":
//             return LLMServiceIdentifier.OPENAI;
//         case "grazie":
//             return LLMServiceIdentifier.GRAZIE;
//         case "lmstudio":
//             return LLMServiceIdentifier.LMSTUDIO;
//         case "deepseek":
//             return LLMServiceIdentifier.DEEPSEEK;
//         case "rango":
//             return LLMServiceIdentifier.RANGO;
//     }
// }
