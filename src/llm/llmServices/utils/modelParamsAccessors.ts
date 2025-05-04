import { ModelParams } from "../modelParams";

export function getModelName(params: ModelParams): string | undefined {
    return "modelName" in params ? (params.modelName as string) : "";
}
