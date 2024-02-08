import { 
    CompletionContext, 
    OpenAiModelParams,
    GrazieModelParams,
    PredefinedCompletionModelParams
} from "./llmService/modelParamsInterfaces";
import { GrazieService } from "./llmService/grazie/grazieService";
import { OpenAiService } from "./llmService/openai/openAiService";
import { 
    PredefinedCompletionService 
} from "./llmService/predefinedCompletion/predefinedCompletionService";

export type Proof = string;
export type ProofBatch = Proof[];

export interface LLMServices {
    openAiService: OpenAiService;
    grazieService: GrazieService;
    predefinedCompletionService: PredefinedCompletionService;
}

export interface ModelsParams {
    openAiParams: OpenAiModelParams[];
    grazieParams: GrazieModelParams[];
    predefinedCompletionParams: PredefinedCompletionModelParams[];
}

type CompletionHook = () => Promise<string[]>;

export class LLMSequentialIterator implements AsyncIterator<Proof> {
    private completionHooks: CompletionHook[];
    private fetchedResults: ProofBatch[];

    private completionHookIndex: number;
    private proofIndex: number;
    
    constructor(
        completionContext: CompletionContext, 
        modelsParams: ModelsParams,
        services: LLMServices,
    ) {
        this.completionHookIndex = 0;
        this.proofIndex = 0;
        this.completionHooks = this.createCompletionHooks(
            completionContext, 
            modelsParams, 
            services
        );
        this.fetchedResults = new Array<ProofBatch>(this.completionHooks.length);
    }

    private createCompletionHooks(
        completionContext: CompletionContext, 
        modelsParams: ModelsParams,
        services: LLMServices
    ): CompletionHook[] {
        const completionHooks: CompletionHook[] = [];
        for (const params of modelsParams.predefinedCompletionParams) {
            completionHooks.push(
                () => services.predefinedCompletionService.requestCompletion(
                    completionContext, 
                    params
                )
            );
        }

        for (const params of modelsParams.openAiParams) {
            completionHooks.push(
                () => services.openAiService.requestCompletion(
                    completionContext, 
                    params
                )
            );
        }

        for (const params of modelsParams.grazieParams) {
            completionHooks.push(
                () => services.grazieService.requestCompletion(
                    completionContext, 
                    params
                )
            );
        }

        return completionHooks;
    }

    [Symbol.asyncIterator]() {
        return this;
    }

    async next(): Promise<IteratorResult<string, any>> {
        if (this.completionHookIndex >= this.completionHooks.length) {
            return { done: true, value: undefined };
        }

        if (this.fetchedResults[this.completionHookIndex] === undefined) {
            this.fetchedResults[this.completionHookIndex] = await this.completionHooks[this.completionHookIndex]();
        }

        if (this.proofIndex >= this.fetchedResults[this.completionHookIndex].length) {
            this.completionHookIndex += 1;
            this.proofIndex = 0;
            return this.next();
        }

        const proof = this.fetchedResults[this.completionHookIndex][this.proofIndex];

        this.proofIndex += 1;

        return { done: false, value: proof };
    }
}