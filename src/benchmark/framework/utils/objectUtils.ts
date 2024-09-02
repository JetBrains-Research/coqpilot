export function hasAllPropertiesDefined<TargetStruct>(
    partial: Partial<TargetStruct>
): partial is TargetStruct {
    const keys = Object.keys(partial) as (keyof TargetStruct)[];
    return keys.every((key) => partial[key] !== undefined);
}
