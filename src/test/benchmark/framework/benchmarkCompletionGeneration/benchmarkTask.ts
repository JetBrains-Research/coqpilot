import { CoqProofChecker } from "../../../../core/coqProofChecker";

import { BenchmarkingItem } from "../structures/benchmarkingItem";
import { selectLLMServiceBuilder } from "../structures/llmServiceIdentifier";

import { generateSingleCompletion } from "./generateSingleCompletion";

/**
 * 1. build all projects with script
 * 2. transform decl tasks into real tasks: real task = 1 target goal to complete
 * - each task holds its source file env
 * - and its process env (coqProofChecker and lsp)
 * - its LLMService! just to isolate + isolate logs
 * 3. 4 async tasks for benchmarking LLMService
 * - (we have global mutex for the working dir of the project)
 * - each runs TASKS_N async tasks with single completion, they run individually
 * - they put their results by themselves
 * 4. return result
 */

export async function benchmarkCompletionGenerationTask(
    benchmarkingItem: BenchmarkingItem
): Promise<void> {
    const llmService = selectLLMServiceBuilder(
        benchmarkingItem.llmServiceIdentifier
    )();
    const task = benchmarkingItem.task;
    try {
        await generateSingleCompletion(
            task.getCompletionContext(),
            task.getSourceFileEnvironment(),
            benchmarkingItem.params,
            llmService,
            new CoqProofChecker(task.preparedEnvironment.coqLspClient)
            // TODO: each coq proof checker should use its own prefix to work good in parallel (many checkers for the same theorem in the same file)
        );
        // TODO: handle service error => wait and retry
        // OTHERWISE:
        // TODO: collect all necessary metrics
        // TODO: build result, save it in file
        // TODO: save it in the parent structure (via reporter)
    } finally {
        llmService.dispose();
    }
}
