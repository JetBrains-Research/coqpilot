import { 
    GrazieModelParams, 
    GrazieServiceParams,
    GrazieRequestParams,
} from '../serviceParams';
import { GrazieApiInterface } from './grazieApiInterface';
import { History } from '../../types';
import { LLM } from '../../llmInterface';

export class GrazieService {
    api: GrazieApiInterface; 

    constructor(api: GrazieApiInterface) {
        this.api = api;
    }

    private async requestCompletion(params: GrazieRequestParams): Promise<string[]> {
        const choices = params.serviceParams.choices;
        let attempts = choices * 2;
        const completions: Promise<string>[] = [];

        while (completions.length < choices && attempts > 0) {
            completions.push(this.api.chatCompletionRequest(params));
            attempts--;
        }

        return Promise.all(completions);
    }

    public createModel(modelParams: GrazieModelParams, serviceParams: GrazieServiceParams): LLM {
        return new class implements LLM {
            constructor(
                public superThis: GrazieService, 
                public modelParams: GrazieModelParams, 
                public serviceParams: GrazieServiceParams
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