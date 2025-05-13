import { TargetsBuilderWithWorkspaceRoot } from "../../../benchmark/framework/experiment/setupDSL/targetsBuilder";
import { unreachable } from "../../../utils/errors/throwErrors";

export type TestTargetType = "admit" | "prove theorem";

export function withTargetsFromFile(
    contructedBundle: TargetsBuilderWithWorkspaceRoot,
    targetType: TestTargetType,
    filePath: string,
    ...theoremNames: string[]
): TargetsBuilderWithWorkspaceRoot {
    if (targetType === "admit") {
        return contructedBundle.withAdmitTargetsFromFile(
            filePath,
            ...theoremNames
        );
    } else if (targetType === "prove theorem") {
        return contructedBundle.withProveTheoremTargetsFromFile(
            filePath,
            ...theoremNames
        );
    }
    unreachable(`unknown target type: "${targetType}"`);
}
