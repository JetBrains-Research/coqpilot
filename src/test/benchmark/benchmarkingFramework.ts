import { expect } from "earl";

import { LLMServices } from "../../llm/llmServices";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import { ModelParams, ModelsParams } from "../../llm/llmServices/modelParams";
import { OpenAiService } from "../../llm/llmServices/openai/openAiService";
import { PredefinedProofsService } from "../../llm/llmServices/predefinedProofs/predefinedProofsService";

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
import { resolveParametersOrThrow } from "../commonTestFunctions/resolveOrThrow";

import { InputModelsParams } from "./inputModelsParams";
import { consoleLog, consoleLogSeparatorLine } from "./loggingUtils";
import { Results } from "./results";

export async function runTestBenchmark(
    filePath: string,
    inputModelsParams: InputModelsParams,
    specificTheoremsForBenchmark: string[] | undefined,
    benchmarkFullTheorems: Boolean = true,
    benchmarkAdmits: Boolean = true,
    workspaceRootPath?: string,
    requireAllAdmitsCompleted: Boolean = false
): Promise<Results.BenchmarkingSummary> {
    consoleLog(`run benchmarks for file: ${filePath}\n`, "blue");
    const shouldCompleteHole = (_hole: ProofStep) => true;

    const [completionTargets, sourceFileEnvironment, processEnvironment] =
        await prepareForBenchmarkCompletions(
            inputModelsParams,
            shouldCompleteHole,
            workspaceRootPath,
            filePath
        );
    const filteredCompletionTargets = {
        admitTargets: completionTargets.admitTargets.filter(
            (target) =>
                specificTheoremsForBenchmark?.includes(
                    target.parentTheorem.name
                ) ?? true
        ),
        theoremTargets: completionTargets.theoremTargets.filter(
            (target) =>
                specificTheoremsForBenchmark?.includes(
                    target.parentTheorem.name
                ) ?? true
        ),
    };

    consoleLogSeparatorLine("\n");

    let admitTargetsResults: Results.ApproachBenchmarkingSummary | undefined =
        undefined;
    let theoremTargetsResults: Results.ApproachBenchmarkingSummary | undefined =
        undefined;

    if (benchmarkAdmits) {
        consoleLog("try to complete admits\n");
        admitTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.admitTargets,
            filePath,
            sourceFileEnvironment,
            processEnvironment
        );
        consoleLog(
            `BENCHMARK RESULT, ADMITS COMPLETED: ${admitTargetsResults}\n`
        );
        consoleLogSeparatorLine("\n");

        if (requireAllAdmitsCompleted) {
            expect(admitTargetsResults.allSuccessful()).toBeTruthy();
        }
    }

    if (benchmarkFullTheorems) {
        consoleLog("try to prove theorems\n");
        theoremTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.theoremTargets,
            filePath,
            sourceFileEnvironment,
            processEnvironment
        );
        consoleLog(
            `BENCHMARK RESULT, THEOREMS PROVED: ${theoremTargetsResults}\n`
        );
        consoleLogSeparatorLine();
    }

    return {
        admitsCompletions: admitTargetsResults,
        theoremsCompletions: theoremTargetsResults,
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
    admitsCompleted?: BenchmarkResult;
    theoremsProved?: BenchmarkResult;
}

export async function benchmarkTargets(
    targets: BenchmarkingCompletionContext[],
    filePath: string,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<Results.ApproachBenchmarkingSummary> {
    const tasksMap: Map<
        Results.CompletionGenerationTask,
        Map<string, Results.LLMServiceBenchmarkingResult<ModelParams>>
    > = new Map();

    for (const completionContext of targets) {
        const task: Results.CompletionGenerationTask = {
            sourceTheorem: new Results.RichTheorem(
                completionContext.parentTheorem,
                filePath
            ),
            targetGoal: goalToString(completionContext.proofGoal),
            targetEndPosition: completionContext.admitEndPosition,
        };
        const llmServicesResultsMap =
            await benchmarkCompletionGenerationWithEachLLMService(
                task,
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            );
        tasksMap.set(task, llmServicesResultsMap);
    }
    return new Results.ApproachBenchmarkingSummary(tasksMap);
}

async function benchmarkCompletionGenerationWithEachLLMService(
    task: Results.CompletionGenerationTask,
    completionContext: BenchmarkingCompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<Map<string, Results.LLMServiceBenchmarkingResult<ModelParams>>> {
    return new Map([
        [
            processEnvironment.services.predefinedProofsService.serviceName,
            await benchmarkCompletionGenerationWithEachModel(
                processEnvironment.modelsParams.predefinedProofsModelParams,
                task,
                processEnvironment.services.predefinedProofsService.serviceName,
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            ),
        ],
        [
            processEnvironment.services.openAiService.serviceName,
            await benchmarkCompletionGenerationWithEachModel(
                processEnvironment.modelsParams.openAiParams,
                task,
                processEnvironment.services.openAiService.serviceName,
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            ),
        ],
        [
            processEnvironment.services.grazieService.serviceName,
            await benchmarkCompletionGenerationWithEachModel(
                processEnvironment.modelsParams.grazieParams,
                task,
                processEnvironment.services.grazieService.serviceName,
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            ),
        ],
        [
            processEnvironment.services.lmStudioService.serviceName,
            await benchmarkCompletionGenerationWithEachModel(
                processEnvironment.modelsParams.lmStudioParams,
                task,
                processEnvironment.services.lmStudioService.serviceName,
                completionContext,
                sourceFileEnvironment,
                processEnvironment
            ),
        ],
    ]);
}

async function benchmarkCompletionGenerationWithEachModel(
    models: ModelParams[],
    task: Results.CompletionGenerationTask,
    llmServiceName: string,
    completionContext: BenchmarkingCompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<Results.LLMServiceBenchmarkingResult<ModelParams>> {
    const modelsResultsMap: Map<
        ModelParams,
        Results.BenchmarkingResult<ModelParams>
    > = new Map();
    for (const model of models) {
        modelsResultsMap.set(model, {
            task: task,
            llmServiceName: llmServiceName,
            modelParams: model,
            result: await benchmarkCompletionGeneration(
                completionContext,
                sourceFileEnvironment,
                processEnvironment // !!!! only one model should be passed here
            ),
        });
    }
    return modelsResultsMap;
}

async function benchmarkCompletionGeneration(
    completionContext: BenchmarkingCompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment
): Promise<Results.CompletionGenerationResult> {
    const completionPosition = completionContext.admitEndPosition;
    consoleLog(
        `Completion position: ${completionPosition.line}:${completionPosition.character}`
    );
    consoleLog(`Theorem name: \`${completionContext.parentTheorem.name}\``);
    consoleLog(`Proof goal: \`${goalToString(completionContext.proofGoal)}\``);

    const sourceFileEnvironmentWithFilteredContext: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => completionContext.parentTheorem !== thr
        ),
    };

    const startTime = performance.now();
    const completionResult = await generateCompletion(
        completionContext,
        sourceFileEnvironmentWithFilteredContext,
        processEnvironment
    );
    const endTime = performance.now();

    const benchmarkingResult: Results.CompletionGenerationResult = {
        successfullyGeneratedCompletion: false,
        elapsedTimeMillis: Math.round(endTime - startTime),
        contextTheorems: [], // TODO: support
        requestChatTokens: 0, // TODO: support
    };

    let message = "unknown";
    if (completionResult instanceof SuccessGenerationResult) {
        message = `Success: ${completionResult.data}`;
        benchmarkingResult.successfullyGeneratedCompletion = true;
    } else if (completionResult instanceof FailureGenerationResult) {
        switch (completionResult.status) {
            case FailureGenerationStatus.TIMEOUT_EXCEEDED:
                message = "Timeout";
                break;
            case FailureGenerationStatus.ERROR_OCCURRED:
                message = `Exception: ${completionResult.message}`;
                break;
            case FailureGenerationStatus.SEARCH_FAILED:
                message = "Proofs not found";
                break;
        }
    }
    consoleLog(
        message,
        benchmarkingResult.successfullyGeneratedCompletion ? "green" : "red"
    );
    consoleLog(
        `elapsedTime: ${benchmarkingResult.elapsedTimeMillis} ms`,
        "gray"
    );
    consoleLog("");

    return benchmarkingResult;
}

function goalToString(proofGoal: Goal<PpString>): string {
    return `${proofGoal?.ty}`;
}

async function prepareForBenchmarkCompletions(
    inputModelsParams: InputModelsParams,
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
        modelsParams: resolveInputModelsParametersOrThrow(
            inputModelsParams,
            llmServices
        ),
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

function resolveInputModelsParametersOrThrow(
    inputModelsParams: InputModelsParams,
    llmServices: LLMServices
): ModelsParams {
    return {
        predefinedProofsModelParams:
            inputModelsParams.predefinedProofsModelParams.map((inputParams) =>
                resolveParametersOrThrow(
                    llmServices.predefinedProofsService,
                    inputParams
                )
            ),
        openAiParams: inputModelsParams.openAiParams.map((inputParams) =>
            resolveParametersOrThrow(llmServices.openAiService, inputParams)
        ),
        grazieParams: inputModelsParams.grazieParams.map((inputParams) =>
            resolveParametersOrThrow(llmServices.grazieService, inputParams)
        ),
        lmStudioParams: inputModelsParams.lmStudioParams.map((inputParams) =>
            resolveParametersOrThrow(llmServices.lmStudioService, inputParams)
        ),
    };
}
