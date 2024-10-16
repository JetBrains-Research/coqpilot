export function throwOnTheoremWithoutInitialGoal(
    theoremName: string,
    filePath: string
): never {
    throw Error(
        [
            `internal invariant failed: targets should be extracted only `,
            `from theorems with proofs, that should guarantee \`initial_goal\` being present; `,
            `however, the theorem "${theoremName}" from the ${filePath} file `,
            `has undefined \`initial_goal\``,
        ].join("")
    );
}
