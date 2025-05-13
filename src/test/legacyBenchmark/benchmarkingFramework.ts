import * as assert from "assert";
import * as fs from "fs";

import { GenerationBundlesStorage } from "../../llm/generationBundles";
import { ErrorsHandlingMode } from "../../llm/llmServices/commonStructures/errorsHandlingMode";
import { isLLMServiceRequestSucceeded } from "../../llm/llmServices/commonStructures/llmServiceRequest";
import { LLMServiceImpl } from "../../llm/llmServices/llmService";
import { selectLLMServiceProvider } from "../../llm/llmServices/llmServiceProvider";
import { ModelParams } from "../../llm/llmServices/modelParams";
import { LLMServiceControlParams } from "../../llm/llmServices/utils/llmServiceControlParams";
import { resolveParametersOrThrow } from "../../llm/llmServices/utils/resolveOrThrow";
import { LLMServicesStorage } from "../../llm/llmServicesStorage";

import { withDocumentOpenedByTestCoqLsp } from "../../coqLsp/coqLspBuilders";
import { CoqLspClient } from "../../coqLsp/coqLspClient";
import { ProofGoal } from "../../coqLsp/coqLspTypes";

import {
    CompletionContext,
    ProcessEnvironment,
    SourceFileEnvironment,
    TargetType,
} from "../../core/completionGenerationContext";
import {
    FailureGenerationResult,
    FailureGenerationStatus,
    SuccessGenerationResult,
    generateCompletion,
} from "../../core/completionGenerator";
import { CoqProofChecker } from "../../core/coqProofChecker";
import { createSourceFileEnvironment } from "../../core/inspectSourceFile";

import { ProofStep, Theorem } from "../../coqParser/parsedTypes";
import { EventLogger } from "../../logging/eventLogger";
import { illegalState, throwError } from "../../utils/errors/throwErrors";
import { stringifyAnyValue } from "../../utils/printers";
import { ProjectRoot } from "../../utils/structures/projectRoot";
import { Uri } from "../../utils/structures/uri";

import { AdditionalFileImport } from "./additionalImports";
import { InputModelsParams } from "./inputModelsParams";
import { BenchmarkReportHolder, TheoremProofResult } from "./reportHolder";
import { consoleLog, consoleLogSeparatorLine } from "./utils/loggingUtils";

export interface TestBenchmarkOptions extends TestBenchmarkOptionsWithDefaults {
    filePath: string;
    // TODO: support ranker
    inputModelsParams: InputModelsParams;
    relativePathToFile: string;
}

export interface TestBenchmarkOptionsWithDefaults {
    specificTheoremsForBenchmark: string[] | undefined;
    benchmarkFullTheorems: Boolean;
    benchmarkAdmits: Boolean;
    workspaceRootPath?: string;
    requireAllAdmitsCompleted: Boolean;
    maxPremisesNumber?: number;
    groupName: string;
    reportHolder?: BenchmarkReportHolder;
    additionalImports?: AdditionalFileImport[];
    perProofTimeoutMillis: number;
}

export function resolveTestBenchmarkOptionsWithDefaults(
    inputOptions: TestBenchmarkOptions &
        Partial<TestBenchmarkOptionsWithDefaults>
): TestBenchmarkOptions {
    return {
        ...inputOptions,
        benchmarkFullTheorems: inputOptions.benchmarkFullTheorems ?? true,
        benchmarkAdmits: inputOptions.benchmarkAdmits ?? true,
        requireAllAdmitsCompleted:
            inputOptions.requireAllAdmitsCompleted ?? false,
        groupName: inputOptions.groupName ?? "Unnamed",
        perProofTimeoutMillis: inputOptions.perProofTimeoutMillis ?? 15_000,
    };
}

export async function runTestBenchmark(
    inputOptions: TestBenchmarkOptions
): Promise<BenchmarkReport> {
    const resolvedOptions =
        resolveTestBenchmarkOptionsWithDefaults(inputOptions);

    const [fileUri, isNewlyCreatedFile] = getFileUriWithImports(
        resolvedOptions.filePath,
        resolvedOptions.additionalImports
    );
    /**
     * Note: so far the abort signal is never triggered;
     * however, such behaviour can be supported:
     * the same `AbortController` object is passed throughout the run properly.
     */
    const abortController = new AbortController();

    return withDocumentOpenedByTestCoqLsp(
        { uri: fileUri },
        {
            workspaceRootPath: inputOptions.workspaceRootPath,
            abortSignal: abortController.signal,
        },
        async (coqLspClient) => {
            // TODO: for more efficiency, `llmServices` should be created only once and top-level
            const eventLogger = new EventLogger();
            const llmServices = createLLMServices(
                resolvedOptions.inputModelsParams,
                eventLogger
            );
            try {
                return await runTestBenchmarkOnPreparedFile(
                    resolvedOptions,
                    llmServices,
                    coqLspClient,
                    fileUri,
                    resolvedOptions.workspaceRootPath === undefined
                        ? undefined
                        : Uri.fromPath(resolvedOptions.workspaceRootPath),
                    isNewlyCreatedFile,
                    abortController,
                    eventLogger
                );
            } finally {
                llmServices.dispose();
            }
        }
    );
}

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
    const updatedFileContent = importStrings.join("\n") + "\n" + fileContent;
    const auxFilePath = buildAuxFileUri(filePath);
    fs.writeFileSync(auxFilePath.fsPath, updatedFileContent);
    return [auxFilePath, true];
}

export async function runTestBenchmarkOnPreparedFile(
    options: TestBenchmarkOptions,
    llmServices: LLMServicesStorage,
    coqLspClient: CoqLspClient,
    fileUri: Uri,
    workspaceRootUri: Uri | undefined,
    isNewlyCreatedFile: boolean,
    abortController: AbortController,
    eventLogger: EventLogger
): Promise<BenchmarkReport> {
    consoleLog(`run benchmarks for file: ${options.filePath}\n`, "blue");
    const shouldCompleteHole = (_hole: ProofStep) => true;

    const [completionTargets, sourceFileEnvironment, processEnvironment] =
        await prepareForBenchmarkCompletions(
            options.inputModelsParams,
            llmServices,
            shouldCompleteHole,
            coqLspClient,
            fileUri,
            workspaceRootUri,
            isNewlyCreatedFile
        );
    const filteredCompletionTargets = {
        admitTargets: completionTargets.admitTargets.filter(
            (target) =>
                options.specificTheoremsForBenchmark?.includes(
                    target.sourceTheorem.name
                ) ?? true
        ),
        theoremTargets: completionTargets.theoremTargets.filter(
            (target) =>
                options.specificTheoremsForBenchmark?.includes(
                    target.sourceTheorem.name
                ) ?? true
        ),
    };

    consoleLogSeparatorLine("\n");

    let admitTargetsResults: BenchmarkResult | undefined = undefined;
    let theoremTargetsResults: BenchmarkResult | undefined = undefined;

    if (options.benchmarkAdmits) {
        consoleLog("try to complete admits\n");
        admitTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.admitTargets,
            sourceFileEnvironment,
            processEnvironment,
            getSingleModelId(options.inputModelsParams),
            options.relativePathToFile,
            options.groupName,
            abortController,
            eventLogger,
            options.maxPremisesNumber,
            options.reportHolder,
            options.perProofTimeoutMillis
        );
        consoleLog(
            `BENCHMARK RESULT, ADMITS COMPLETED: ${admitTargetsResults}\n`
        );
        consoleLogSeparatorLine("\n");

        if (options.requireAllAdmitsCompleted) {
            assert.ok(admitTargetsResults.allCompleted());
        }
    }

    if (options.benchmarkFullTheorems) {
        consoleLog("try to prove theorems\n");
        theoremTargetsResults = await benchmarkTargets(
            filteredCompletionTargets.theoremTargets,
            sourceFileEnvironment,
            processEnvironment,
            getSingleModelId(options.inputModelsParams),
            options.relativePathToFile,
            options.groupName,
            abortController,
            eventLogger,
            options.maxPremisesNumber,
            options.reportHolder,
            options.perProofTimeoutMillis
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
    const modelIds = inputModelsParams
        .flatMap((item) => item.models)
        .map((model) => model.modelId);
    if (modelIds.length !== 1) {
        throwError(`expected exactly one model id, but got ${modelIds.length}`);
    }

    return modelIds[0];
}

export interface BenchmarkingCompletionTargets {
    admitTargets: CompletionContext[];
    theoremTargets: CompletionContext[];
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
    targets: CompletionContext[],
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    modelId: string,
    checkedFilePath: string,
    groupName: string,
    abortController: AbortController,
    eventLogger: EventLogger,
    maxPremisesNumber?: number,
    reportHolder?: BenchmarkReportHolder,
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
            abortController,
            eventLogger,
            maxPremisesNumber,
            reportHolder,
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
    completionContext: CompletionContext,
    sourceFileEnvironment: SourceFileEnvironment,
    processEnvironment: ProcessEnvironment,
    modelId: string,
    checkedFilePath: string,
    groupName: string,
    abortController: AbortController,
    eventLogger: EventLogger,
    maxPremisesNumber?: number,
    reportHolder?: BenchmarkReportHolder,
    perProofTimeoutMillis: number = 15000
): Promise<boolean> {
    const completionPosition = completionContext.admitRange.start;
    consoleLog(
        `Completion position: ${completionPosition.line}:${completionPosition.character}`
    );
    consoleLog(`Theorem name: \`${completionContext.sourceTheorem.name}\``);
    consoleLog(`Proof goal: \`${goalToString(completionContext.proofGoal)}\``);

    const sourceFileEnvironmentWithFilteredContext: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => completionContext.sourceTheorem.name !== thr.name
        ),
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

    const processEnvironmentWithPremisesNumber: ProcessEnvironment = {
        ...processEnvironment,
        premisesNumber: maxPremisesNumber,
    };

    const result = await generateCompletion(
        completionContext,
        sourceFileEnvironmentWithFilteredContext,
        processEnvironmentWithPremisesNumber,
        abortController.signal,
        undefined,
        perProofTimeoutMillis
    );
    let message = "unknown";
    let success = false;
    if (result instanceof SuccessGenerationResult) {
        message = `Success: ${result.data}`;
        success = true;

        const proofStats: TheoremProofResult = {
            theoremName: completionContext.sourceTheorem.name,
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

function goalToString(proofGoal: ProofGoal): string {
    return `${proofGoal?.ty}`;
}

interface ContextTheoremsHolder {
    contextTheorems?: string[];
}

function reactToRequestEvent(
    contextTheorems: ContextTheoremsHolder
): (data: any) => void {
    return (data: any) => {
        if (!isLLMServiceRequestSucceeded(data)) {
            illegalState(
                `data of the ${LLMServiceImpl.requestSucceededEvent} event `,
                "should be a `LLMServiceRequestSucceeded` object, but got: ",
                stringifyAnyValue(data)
            );
        }
        contextTheorems.contextTheorems = data.analyzedChat?.contextTheorems;
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
    llmServices: LLMServicesStorage,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    coqLspClient: CoqLspClient,
    fileUri: Uri,
    workspaceRootUri: Uri | undefined,
    isNewlyCreatedFile: boolean
): Promise<
    [BenchmarkingCompletionTargets, SourceFileEnvironment, ProcessEnvironment]
> {
    const coqProofChecker = new CoqProofChecker(coqLspClient);
    const mockDocumentVersion = 1;
    const [completionTargets, sourceFileEnvironment] =
        await extractCompletionTargets(
            mockDocumentVersion,
            shouldCompleteHole,
            fileUri,
            workspaceRootUri,
            coqLspClient,
            true // TODO: pass `ranker.needsUnwrappedNotations` here
        );

    const bundles = resolveParamsAndCreateBundles(
        inputModelsParams,
        llmServices
    );
    const processEnvironment: ProcessEnvironment = {
        coqProofChecker: coqProofChecker,
        bundles: bundles,
    };

    if (isNewlyCreatedFile) {
        fs.unlinkSync(fileUri.fsPath);
    }

    return [completionTargets, sourceFileEnvironment, processEnvironment];
}

async function extractCompletionTargets(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileUri: Uri,
    workspaceRootUri: Uri | undefined,
    client: CoqLspClient,
    rankerNeedsUnwrappedNotations: boolean
): Promise<[BenchmarkingCompletionTargets, SourceFileEnvironment]> {
    const abortController = new AbortController();
    const projectRoot: ProjectRoot | undefined =
        workspaceRootUri === undefined
            ? undefined
            : {
                  uri: workspaceRootUri,
                  requiresNixEnvironment: false, // TODO: support specifying top-level
              };
    const sourceFileEnvironment = await createSourceFileEnvironment(
        documentVersion,
        fileUri,
        projectRoot,
        client,
        abortController.signal,
        rankerNeedsUnwrappedNotations
    );
    const completionTargets = await createCompletionTargets(
        documentVersion,
        shouldCompleteHole,
        sourceFileEnvironment.fileTheorems,
        fileUri,
        client
    );
    const sourceFileEnvironmentWithCompleteProofs: SourceFileEnvironment = {
        ...sourceFileEnvironment,
        fileTheorems: sourceFileEnvironment.fileTheorems.filter(
            (thr) => !thr.proof.is_incomplete
        ),
    };

    return [completionTargets, sourceFileEnvironmentWithCompleteProofs];
}

interface ParentedProofStep {
    parentTheorem: Theorem;
    proofStep: ProofStep;
}

async function createCompletionTargets(
    documentVersion: number,
    shouldCompleteHole: (hole: ProofStep) => boolean,
    fileTheorems: Theorem[],
    fileUri: Uri,
    client: CoqLspClient
): Promise<BenchmarkingCompletionTargets> {
    const theoremsWithProofs = fileTheorems.filter((thr) => thr.proof);
    const admitHolesToComplete = theoremsWithProofs
        .map((thr) =>
            thr.proof.holes.map((hole) => {
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
            proofStep: thr.proof.proof_steps[1],
        };
    });

    return {
        admitTargets: await resolveProofStepsToCompletionContexts(
            admitHolesToComplete,
            TargetType.ADMIT,
            documentVersion,
            fileUri,
            client
        ),
        theoremTargets: await resolveProofStepsToCompletionContexts(
            firstProofSteps,
            TargetType.PROVE_THEOREM,
            documentVersion,
            fileUri,
            client
        ),
    };
}

async function resolveProofStepsToCompletionContexts(
    parentedProofSteps: ParentedProofStep[],
    targetType: TargetType,
    documentVersion: number,
    fileUri: Uri,
    client: CoqLspClient
): Promise<CompletionContext[]> {
    let completionContexts: CompletionContext[] = [];
    for (const parentedProofStep of parentedProofSteps) {
        const goals = await client.getGoalsAtPoint(
            parentedProofStep.proofStep.range.start,
            fileUri,
            documentVersion
        );
        if (goals.ok && goals.val.length !== 0) {
            completionContexts.push({
                proofGoal: goals.val[0],
                admitRange: parentedProofStep.proofStep.range,
                sourceTheorem: parentedProofStep.parentTheorem,
                targetType: targetType,
            });
        }
    }
    return completionContexts;
}

function createLLMServices(
    inputModelsParams: InputModelsParams,
    eventLogger: EventLogger
): LLMServicesStorage {
    const controlParams: LLMServiceControlParams = {
        eventLogger: eventLogger,
        errorsHandlingMode: ErrorsHandlingMode.RETHROW_ERRORS,
    };
    const llmServices = new LLMServicesStorage();
    try {
        const requestedIdentifiers = new Set(
            inputModelsParams.map((item) => item.identifier)
        );
        for (const identifier of requestedIdentifiers) {
            llmServices.registerService(() =>
                selectLLMServiceProvider(identifier, {})(controlParams)
            );
        }
        return llmServices;
    } catch (e) {
        llmServices.dispose();
        throw e;
    }
}

function resolveParamsAndCreateBundles(
    inputModelsParams: InputModelsParams,
    llmServices: LLMServicesStorage
) {
    const bundles = new GenerationBundlesStorage<ModelParams>();
    for (const { identifier, models } of inputModelsParams) {
        const sameTypeLLMServices = llmServices.getServices(identifier);
        for (const llmService of sameTypeLLMServices) {
            const resolvedModels = models.map((inputModel) =>
                resolveParametersOrThrow(llmService, inputModel)
            );
            bundles.addBundle({
                llmService: llmService,
                models: resolvedModels,
            });
        }
    }
    return bundles;
}
