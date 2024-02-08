import OpenAI from 'openai';
import { 
    OpenAiModelParams, 
    OpenAiRequestParams, 
    OpenAiServiceParams
} from './serviceParams';
import { History } from '../types';
import { LLM } from '../llmInterface';

export class OpenAiService { 
    constructor() {}
    
    private createHistory = (history: History, prompt: string): History => {
        return [{role: 'system', content: prompt}, ...history];
    };

    private async requestCompletion(params: OpenAiRequestParams): Promise<string[]> {
        // Add retry, add logging
        const openai = new OpenAI({ apiKey: params.modelParams.apiKey });
        const completion = await openai.chat.completions.create({
            messages: this.createHistory(params.history, params.modelParams.prompt),
            model: params.modelParams.model,
            n: params.serviceParams.choices,
            temperature: params.modelParams.temperature,
            // eslint-disable-next-line @typescript-eslint/naming-convention
            max_tokens: params.modelParams.maxTokens, 
        });
        
        return completion.choices.map((choice: any) => choice.message.content);
    }

    public createModel(modelParams: OpenAiModelParams, serviceParams: OpenAiServiceParams): LLM {
        return new class implements LLM {
            constructor(
                public superThis: OpenAiService, 
                public modelParams: OpenAiModelParams, 
                public serviceParams: OpenAiServiceParams
            ) {}
            
            async fetchMessage(history: History): Promise<string[]> {
                return this.superThis.requestCompletion({
                    serviceParams: this.serviceParams,
                    modelParams: this.modelParams,
                    history: history
                });
            }
            
            dispose(): void {
                return;
            }
        }(this, modelParams, serviceParams);
    } 
}