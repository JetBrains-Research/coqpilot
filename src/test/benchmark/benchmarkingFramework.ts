import * as assert from "assert";

import { LLMServices } from "../../llm/llmServices";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";
import { UserModelsParams } from "../../llm/userModelParams";

import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { CoqLspConfig } from "../../coqLsp/coqLspConfig";
import { Goal, PpString } from "../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    FailureGenerationResult,
    FailureGenerationStatus,
    ProcessEnvironment,
    SourceFileEnvironment,
    SuccessGenerationResult,
    generateCompletion,
} from "../../core/completionGenerator";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { createSourceFileEnvironment } from "../../core/inspectSourceFile";

import { ProofStep, Theorem } from "../../coqParser/parsedTypes";
import { Uri } from "../../utils/uri";

import { consoleLog, consoleLogLine } from "./loggingUtils";

export async function runTestBenchmark(
    filePath: string,
    modelsParams: UserModelsParams,
    workspaceRootPath?: string,
    requireAllAdmitsCompleted: Boolean = false
): Promise<BenchmarkReport> {
    consoleLog(`run benchmarks for file: ${filePath}\n`, "blue");
    const shouldCompleteHole = (_hole: ProofStep) => true;

    const [completionTargets, sourceFileEnvironment, processEnvironment] =
        await prepareForBenchmarkCompletions(
            modelsParams,
            shouldCompleteHole,
            workspaceRootPath,
            filePath
        );

    consoleLogLine("\n");
    console.log("try to complete admits\n");
    const admitTargetsResults = await benchmarkTargets(
        completionTargets.admitTargets,
        sourceFileEnvironment,
        processEnvironment
    );
    console.log(`BENCHMARK RESULT, ADMITS COMPLETED: ${admitTargetsResults}\n`);
    consoleLogLine("\n");

    console.log("try to prove theorems\n");
    const theoremTargetsResults = await benchmarkTargets(
        completionTargets.theoremTargets,
        sourceFileEnvironment,
        processEnvironment
    );
    console.log(
        `BENCHMARK RESULT, THEOREMS PROVED: ${theoremTargetsResults}\n`
    );
    consoleLogLine();

    if (requireAllAdmitsCompleted) {
        assert.ok(admitTargetsResults.allCompleted());
    }

    return {
        admitsCompleted: admitTargetsResults,
        theoremsProved: theoremTargetsResults,
    };
}

export interface BenchmarkingCompletionContext extends CompletionContext {
    parentTheorem: Theorem;
}

export interface BenchmarkingCompletionTargets {
    admitTargets: BenchmarkingCompletionContext[];
    theoremTargets: BenchmarkingCompletionContext[];
}

export class BenchmarkResult {
    constructor(
        public totalCompletionsNumber: number,
        public successfulCompletionsNumber: number
    ) {}

    toString = (): string => {
        return `${this.successfulCompletionsNumber} / ${this.totalCompletionsNumber}`;
    };

    allCompleted(): Boolean {
        return this.totalCompletionsNumber === this.successfulCompletionsNumber;
    }

    add(other: BenchmarkResult) {
        this.totalCompletionsNumber += other.totalCompletionsNumber;
        this.successfulCompletionsNumber += other.successfulCompletionsNumber;
    }
}

export interface BenchmarkReport {
    admitsCompleted: BenchmarkResult;
    theoremsProved: BenchmarkResult;
}

export async function benchmarkTargets(
    targets: BenchmarkingCompletionContext[],
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<BenchmarkResult> {
    const totalCompletionsNumber = targets.length;
    let successfulCompletionsNumber = 0;
    for (const completionContext of targets) {
        const success = await benchmarkCompletionGeneration(
            completionContext,
            sourceFileEnvironment,
            processEnvironment
        );
        if (success) {
            successfulCompletionsNumber += 1;
        }
    }
    return new BenchmarkResult(
        totalCompletionsNumber,
        successfulCompletionsNumber
    );
}

async function benchmarkCompletionGeneration(
    completionContext: BenchmarkingCompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<boolean> {
    const completionPosition = completionContext.admitEndPosition;
    console.log(
        `Completion position: ${completionPosition.line}:${completionPosition.character}`
    );
    console.log(`Theorem name: \`${completionContext.parentTheorem.name}\``);
    console.log(`Proof goal: \`${goalToString(completionContext.proofGoal)}\``);

    const sourceFileEnvironmentWithFilteredContext: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => completionContext.parentTheorem !== thr
        ),
    };

    const result = await generateCompletion(
        completionContext,
        sourceFileEnvironmentWithFilteredContext,
        processEnvironment
    );
    let message = "unknown";
    let success = false;
    if (result instanceof SuccessGenerationResult) {
        message = `Success: ${result.data}`;
        success = true;
    } else if (result instanceof FailureGenerationResult) {
        switch (result.status) {
            case FailureGenerationStatus.excededTimeout:
                message = "Timeout";
                break;
            case FailureGenerationStatus.exception:
                message = `Exception: ${result.message}`;
                break;
            case FailureGenerationStatus.searchFailed:
                message = "Proofs not found";
                break;
        }
    }
    consoleLog(message, success ? "green" : "red");
    console.log("");
    return success;
}

function goalToString(proofGoal: Goal<PpString>): string {
    return `${proofGoal?.ty}`;
}

async function prepareForBenchmarkCompletions(
    modelsParams: UserModelsParams,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    workspaceRootPath: string | undefined,
    filePath: string
): Promise<
    [BenchmarkingCompletionTargets, SourceFileEnvironment, ProcessEnvironment]
> {
    const fileUri = Uri.fromPath(filePath);

    const client = createCoqLspClient(workspaceRootPath);
    await client.openTextDocument(fileUri);

    const coqProofChecker = new CoqProofChecker(client);
    const mockFileVersion = 1;
    const [completionTargets, sourceFileEnvironment] =
        await extractCompletionTargets(
            mockFileVersion,
            shouldCompleteHole,
            fileUri,
            client
        );
    const llmServices: LLMServices = {
        openAiService: new OpenAiService(),
        grazieService: new GrazieService(),
        predefinedProofsService: new PredefinedProofsService(),
        lmStudioService: new LMStudioService(),
    };
    const processEnvironment: ProcessEnvironment = {
        coqProofChecker: coqProofChecker,
        modelsParams: modelsParams,
        services: llmServices,
    };

    return [completionTargets, sourceFileEnvironment, processEnvironment];
}

function createCoqLspClient(workspaceRootPath?: string): CoqLspClient {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig(
        process.env.COQ_LSP_PATH || "coq-lsp",
        workspaceRootPath
    );
    return new CoqLspClient(coqLspServerConfig, coqLspClientConfig);
}

async function extractCompletionTargets(
    fileVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri,
    client: CoqLspClient
): Promise<[BenchmarkingCompletionTargets, SourceFileEnvironment]> {
    const sourceFileEnvironment = await createSourceFileEnvironment(
        fileVersion,
        fileUri,
        client
    );
    const completionTargets = await createCompletionTargets(
        fileVersion,
        shouldCompleteHole,
        sourceFileEnvironment.fileTheorems,
        fileUri,
        client
    );
    const sourceFileEnvironmentWithCompleteProofs: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => thr.proof && !thr.proof.is_incomplete
        ),
    };

    return [completionTargets, sourceFileEnvironmentWithCompleteProofs];
}

interface ParentedProofStep {
    parentTheorem: Theorem;
    proofStep: ProofStep;
}

async function createCompletionTargets(
    fileVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileTheorems: Theorem[],
    fileUri: Uri,
    client: CoqLspClient
): Promise<BenchmarkingCompletionTargets> {
    const theoremsWithProofs = fileTheorems.filter((thr) => thr.proof);
    const admitHolesToComplete = theoremsWithProofs
        .map((thr) =>
            thr.proof!.holes.map((hole) => {
                return {
                    parentTheorem: thr,
                    proofStep: hole,
                };
            })
        )
        .flat()
        .filter((parentedProofStep) =>
            shouldCompleteHole(parentedProofStep.proofStep)
        );
    const firstProofSteps = theoremsWithProofs.map((thr) => {
        return {
            parentTheorem: thr,
            proofStep: thr.proof!.proof_steps[1],
        };
    });

    return {
        admitTargets: await resolveProofStepsToCompletionContexts(
            admitHolesToComplete,
            fileVersion,
            fileUri,
            client
        ),
        theoremTargets: await resolveProofStepsToCompletionContexts(
            firstProofSteps,
            fileVersion,
            fileUri,
            client
        ),
    };
}

async function resolveProofStepsToCompletionContexts(
    parentedProofSteps: ParentedProofStep[],
    fileVersion: number,
    fileUri: Uri,
    client: CoqLspClient
): Promise<BenchmarkingCompletionContext[]> {
    let completionContexts: BenchmarkingCompletionContext[] = [];
    for (const parentedProofStep of parentedProofSteps) {
        const goal = await client.getFirstGoalAtPoint(
            parentedProofStep.proofStep.range.start,
            fileUri,
            fileVersion
        );
        if (!(goal instanceof Error)) {
            completionContexts.push({
                proofGoal: goal,
                prefixEndPosition: parentedProofStep.proofStep.range.start,
                admitEndPosition: parentedProofStep.proofStep.range.end,
                parentTheorem: parentedProofStep.parentTheorem,
            });
        }
    }
    return completionContexts;
}
