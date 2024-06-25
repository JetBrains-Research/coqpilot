import { stringifyAnyValue } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../logging/benchmarkingLogger";
import { WorkspaceRoot } from "../structures/completionGenerationTask";
import { BuildAndParseCoqProjectBySubprocessSignature } from "../subprocessCalls/buildAndParseCoqProject/callSignature";

import { BaseInputBenchmarkingBundle } from "./experiment";

export type MergedInputTargets = Map<
    WorkspaceRoot,
    BuildAndParseCoqProjectBySubprocessSignature.ArgsModels.FilePathToFileTarget
>;

/**
 * Merges `requestedTargets` of `inputBundles` into new `MergedInputTargets` without modifying themselves.
 */
export function mergeRequestedTargets(
    inputBundles: BaseInputBenchmarkingBundle[],
    logger: BenchmarkingLogger
): MergedInputTargets {
    const mergedTargets = inputBundles.reduce(
        (acc, inputBundle) => mergeTwoRequestedTargets(acc, inputBundle),
        new Map()
    );
    logger.debug(
        `Successfully merged requested targets: ${logMergedInputTargets(mergedTargets)}`
    );
    return mergedTargets;
}

function logMergedInputTargets(mergedInputTargets: MergedInputTargets): string {
    // TODO: support better logging
    return stringifyAnyValue(Array.from(mergedInputTargets.entries()), 2);
}

/**
 * Merges `requestedTargets` of `nextInputBundle` into `mergedTargets`.
 */
function mergeTwoRequestedTargets(
    mergedTargets: MergedInputTargets,
    nextInputBundle: BaseInputBenchmarkingBundle
): MergedInputTargets {
    const bundleId = nextInputBundle.bundleId;
    for (const inputTargets of nextInputBundle.requestedTargets) {
        for (const [workspaceRoot, nextFilePathToFileTargets] of inputTargets) {
            if (!mergedTargets.has(workspaceRoot)) {
                mergedTargets.set(workspaceRoot, {});
            }
            const mergedFilePathToFileTarget =
                mergedTargets.get(workspaceRoot)!;
            for (const [
                filePath,
                nextFileTarget,
            ] of nextFilePathToFileTargets) {
                if (!(filePath in mergedFilePathToFileTarget)) {
                    mergedFilePathToFileTarget[filePath] = {
                        specificTheoremTargets: {},
                        allTheoremsTargetTypes: {
                            ADMIT: [],
                            PROVE_THEOREM: [],
                        },
                    };
                }
                const mergedFileTarget = mergedFilePathToFileTarget[filePath]!;
                if (nextFileTarget.allTheoremsAsAdmitTargets) {
                    pushIfUnique(
                        bundleId,
                        mergedFileTarget.allTheoremsTargetTypes.ADMIT
                    );
                }
                if (nextFileTarget.allTheoremsAsProveTheoremTargets) {
                    pushIfUnique(
                        bundleId,
                        mergedFileTarget.allTheoremsTargetTypes.PROVE_THEOREM
                    );
                }
                for (const [
                    theoremName,
                    nextTheoremTarget,
                ] of nextFileTarget.specificTheoremTargets) {
                    if (
                        !(
                            theoremName in
                            mergedFileTarget.specificTheoremTargets
                        )
                    ) {
                        mergedFileTarget.specificTheoremTargets[theoremName] = {
                            ADMIT: [],
                            PROVE_THEOREM: [],
                        };
                    }
                    const mergedTheoremTarget =
                        mergedFileTarget.specificTheoremTargets[theoremName]!;
                    if (nextTheoremTarget.admitTargets) {
                        pushIfUnique(bundleId, mergedTheoremTarget.ADMIT);
                    }
                    if (nextTheoremTarget.proveTheoremTarget) {
                        pushIfUnique(
                            bundleId,
                            mergedTheoremTarget.PROVE_THEOREM
                        );
                    }
                }
            }
        }
    }
    return mergedTargets;
}

function pushIfUnique<T>(newElement: T, uniqueElements: T[]) {
    if (uniqueElements.findIndex((element) => element === newElement) === -1) {
        uniqueElements.push(newElement);
    }
}
