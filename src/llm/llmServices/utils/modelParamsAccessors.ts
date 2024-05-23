import { ModelParams } from "../modelParams";

export function modelName(params: ModelParams): string | undefined {
    return "modelName" in params ? (params.modelName as string) : "";
}
