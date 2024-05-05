export function modelName(params: any): string | undefined {
    return "modelName" in params ? (params.modelName as string) : "";
}
