import * as assert from "assert";
import * as fs from "fs";

import { LLMServices } from "../../llm/llmServices";
import { GrazieService } from "../../llm/llmServices/grazie/grazieService";
import {
    LLMServiceImpl,
    LLMServiceRequest,
} from "../../llm/llmServices/llmService";
import { LMStudioService } from "../../llm/llmServices/lmStudio/lmStudioService";
import { ModelsParams } from "../../llm/llmServices/modelParams";
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
import { EventLogger } from "../../logging/eventLogger";
import { Uri } from "../../utils/uri";
import { resolveParametersOrThrow } from "../commonTestFunctions/resolveOrThrow";

import { AdditionalFileImport } from "./additionalImports";
import { InputModelsParams } from "./inputModelsParams";
import { BenchmarkReportHolder, TheoremProofResult } from "./reportHolder";
import { consoleLog, consoleLogSeparatorLine } from "./utils/loggingUtils";

export async function runTestBenchmark(
    filePath: string,
    inputModelsParams: InputModelsParams,
    relativePathToFile: string,
    specificTheoremsForBenchmark: string[] | undefined,
    benchmarkFullTheorems: Boolean = true,
    benchmarkAdmits: Boolean = true,
    workspaceRootPath?: string,
    requireAllAdmitsCompleted: Boolean = false,
    maximumUsedPremisesAmount?: number,
    groupName: string = "Unnamed",
    reportHolder?: BenchmarkReportHolder,
    additionalImports?: AdditionalFileImport[],
    perProofTimeoutMillis: number = 15000
): Promise<BenchmarkReport> {
    consoleLog(`run benchmarks for file: ${filePath}\n`, "blue");
    const shouldCompleteHole = (_hole: ProofStep) => true;
    const eventLogger = new EventLogger();

    const [completionTargets, sourceFileEnvironment, processEnvironment] =
        await prepareForBenchmarkCompletions(
            inputModelsParams,
            shouldCompleteHole,
            workspaceRootPath,
            filePath,
            eventLogger,
            additionalImports
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

    let admitTargetsResults: BenchmarkResult | undefined = undefined;
    let theoremTargetsResults: BenchmarkResult | undefined = undefined;

    if (benchmarkAdmits) {
        consoleLog("try to complete admits\n");
        admitTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.admitTargets,
            sourceFileEnvironment,
            processEnvironment,
            getSingleModelId(inputModelsParams),
            relativePathToFile,
            groupName,
            eventLogger,
            maximumUsedPremisesAmount,
            reportHolder,
            workspaceRootPath,
            perProofTimeoutMillis
        );
        consoleLog(
            `BENCHMARK RESULT, ADMITS COMPLETED: ${admitTargetsResults}\n`
        );
        consoleLogSeparatorLine("\n");

        if (requireAllAdmitsCompleted) {
            assert.ok(admitTargetsResults.allCompleted());
        }
    }

    if (benchmarkFullTheorems) {
        consoleLog("try to prove theorems\n");
        theoremTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.theoremTargets,
            sourceFileEnvironment,
            processEnvironment,
            getSingleModelId(inputModelsParams),
            relativePathToFile,
            groupName,
            eventLogger,
            maximumUsedPremisesAmount,
            reportHolder,
            workspaceRootPath,
            perProofTimeoutMillis
        );
        consoleLog(
            `BENCHMARK RESULT, THEOREMS PROVED: ${theoremTargetsResults}\n`
        );
        consoleLogSeparatorLine();
    }

    return {
        admitsCompleted: admitTargetsResults,
        theoremsProved: theoremTargetsResults,
    };
}

function getSingleModelId(inputModelsParams: InputModelsParams): string {
    const modelIds = [
        ...inputModelsParams.predefinedProofsModelParams.map(
            (params) => params.modelId
        ),
        ...inputModelsParams.openAiParams.map((params) => params.modelId),
        ...inputModelsParams.grazieParams.map((params) => params.modelId),
        ...inputModelsParams.lmStudioParams.map((params) => params.modelId),
    ];
    if (modelIds.length !== 1) {
        throw Error(
            `Expected exactly one model id, but got ${modelIds.length}`
        );
    }

    return modelIds[0];
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
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    modelId: string,
    checkedFilePath: string,
    groupName: string,
    eventLogger: EventLogger,
    maximumUsedPremisesAmount?: number,
    reportHolder?: BenchmarkReportHolder,
    workspaceRootPath?: string,
    perProofTimeoutMillis: number = 15000
): Promise<BenchmarkResult> {
    const totalCompletionsNumber = targets.length;
    let successfulCompletionsNumber = 0;
    for (const completionContext of targets) {
        const success = await benchmarkCompletionGeneration(
            completionContext,
            sourceFileEnvironment,
            processEnvironment,
            modelId,
            checkedFilePath,
            groupName,
            eventLogger,
            maximumUsedPremisesAmount,
            reportHolder,
            workspaceRootPath,
            perProofTimeoutMillis
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
    processEnvironment: ProcessEnvironment,
    modelId: string,
    checkedFilePath: string,
    groupName: string,
    eventLogger: EventLogger,
    maximumUsedPremisesAmount?: number,
    reportHolder?: BenchmarkReportHolder,
    workspaceRootPath?: string,
    perProofTimeoutMillis: number = 15000
): Promise<boolean> {
    const completionPosition = completionContext.admitEndPosition;
    consoleLog(
        `Completion position: ${completionPosition.line}:${completionPosition.character}`
    );
    consoleLog(`Theorem name: \`${completionContext.parentTheorem.name}\``);
    consoleLog(`Proof goal: \`${goalToString(completionContext.proofGoal)}\``);

    const sourceFileEnvironmentWithFilteredContext: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems
            .filter((thr) => completionContext.parentTheorem.name !== thr.name)
            .slice(0, maximumUsedPremisesAmount),
    };

    const contextTheorems: ContextTheoremsHolder = {};
    const succeededSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestSucceededEvent,
        reactToRequestEvent(contextTheorems)
    );
    const failedSubscriptionId = eventLogger.subscribeToLogicEvent(
        LLMServiceImpl.requestFailedEvent,
        reactToRequestEvent(contextTheorems)
    );

    const result = await generateCompletion(
        completionContext,
        sourceFileEnvironmentWithFilteredContext,
        processEnvironment,
        undefined,
        workspaceRootPath,
        perProofTimeoutMillis
    );
    let message = "unknown";
    let success = false;
    if (result instanceof SuccessGenerationResult) {
        message = `Success: ${result.data}`;
        success = true;

        const proofStats: TheoremProofResult = {
            theoremName: completionContext.parentTheorem.name,
            filePath: checkedFilePath,
            modelId: modelId,
            generatedProof: result.data,
            chosenPremises: contextTheorems.contextTheorems ?? [],
            generatedAtAttempt: result.attempt,
            group: groupName,
        };
        reportHolder?.addProofResult(proofStats);
    } else if (result instanceof FailureGenerationResult) {
        switch (result.status) {
            case FailureGenerationStatus.TIMEOUT_EXCEEDED:
                message = "Timeout";
                break;
            case FailureGenerationStatus.ERROR_OCCURRED:
                message = `Exception: ${result.message}`;
                break;
            case FailureGenerationStatus.SEARCH_FAILED:
                message = "Proofs not found";
                break;
        }
    }

    eventLogger.unsubscribe(
        LLMServiceImpl.requestSucceededEvent,
        succeededSubscriptionId
    );
    eventLogger.unsubscribe(
        LLMServiceImpl.requestFailedEvent,
        failedSubscriptionId
    );

    consoleLog(message, success ? "green" : "red");
    consoleLog("");
    return success;
}

function goalToString(proofGoal: Goal<PpString>): string {
    return `${proofGoal?.ty}`;
}

interface ContextTheoremsHolder {
    contextTheorems?: string[];
}

function reactToRequestEvent(
    contextTheorems: ContextTheoremsHolder
): (data: any) => void {
    return (data: any) => {
        const request = data as LLMServiceRequest;
        if (request === null) {
            throw Error(
                `Request succeeded event received with null data: ${data}`
            );
        }
        contextTheorems.contextTheorems = request.analyzedChat?.contextTheorems;
    };
}

function buildAuxFileUri(filePath: string, unique: boolean = true): Uri {
    let auxFilePath = filePath.replace(/\.v$/, "_cp_aux.v");
    if (unique && fs.existsSync(auxFilePath)) {
        const randomSuffix = Math.floor(Math.random() * 1000000);
        auxFilePath = auxFilePath.replace(
            /\_cp_aux.v$/,
            `_${randomSuffix}_cp_aux.v`
        );
    }

    return Uri.fromPath(auxFilePath);
}

async function prepareForBenchmarkCompletions(
    inputModelsParams: InputModelsParams,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    workspaceRootPath: string | undefined,
    filePath: string,
    eventLogger: EventLogger,
    additionalImports?: AdditionalFileImport[]
): Promise<
    [BenchmarkingCompletionTargets, SourceFileEnvironment, ProcessEnvironment]
> {
    function getFileUriWithImports(
        filePath: string,
        additionalImports?: AdditionalFileImport[]
    ): [Uri, boolean] {
        if (additionalImports === undefined) {
            return [Uri.fromPath(filePath), false];
        }

        const importStrings =
            additionalImports?.map((importFile) => importFile.get()) ?? [];
        const fileContent = fs.readFileSync(filePath, "utf8");
        const updatedFileContent =
            importStrings.join("\n") + "\n" + fileContent;
        const auxFilePath = buildAuxFileUri(filePath);
        fs.writeFileSync(auxFilePath.fsPath, updatedFileContent);
        return [auxFilePath, true];
    }

    const [fileUri, isNew] = getFileUriWithImports(filePath, additionalImports);

    const client = await createCoqLspClient(workspaceRootPath);
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
        openAiService: new OpenAiService(eventLogger),
        grazieService: new GrazieService(eventLogger),
        predefinedProofsService: new PredefinedProofsService(eventLogger),
        lmStudioService: new LMStudioService(eventLogger),
    };
    const processEnvironment: ProcessEnvironment = {
        coqProofChecker: coqProofChecker,
        modelsParams: resolveInputModelsParametersOrThrow(
            inputModelsParams,
            llmServices
        ),
        services: llmServices,
    };

    if (isNew) {
        fs.unlinkSync(fileUri.fsPath);
    }

    return [completionTargets, sourceFileEnvironment, processEnvironment];
}

async function createCoqLspClient(
    workspaceRootPath?: string
): Promise<CoqLspClient> {
    const coqLspServerConfig = CoqLspConfig.createServerConfig();
    const coqLspClientConfig = CoqLspConfig.createClientConfig(
        process.env.COQ_LSP_PATH || "coq-lsp",
        workspaceRootPath
    );
    return await CoqLspClient.create(coqLspServerConfig, coqLspClientConfig);
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
