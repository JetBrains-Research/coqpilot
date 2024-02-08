import { 
    SingleTacticModelParams
} from './serviceParams';
import { History } from '../types';
import { LLM } from '../llmInterface';

export class SingleTacticService { 
    private requestCompletion(params: SingleTacticModelParams): string[] {
        return this.formatCoqSentences(params.tactics).map((tactic) => {
            return `Proof. ${tactic} Qed.`;
        });
    }

    private formatCoqSentences = (commands: string[]): string[] => {
        return commands.map((command) => {
            if (command.endsWith(".")) {
                return command;
            } else {
                return command + ".";
            }
        });
    };

    public createModel(modelParams: SingleTacticModelParams): LLM {
        return new class implements LLM {
            constructor(
                public superThis: SingleTacticService, 
                public modelParams: SingleTacticModelParams
            ) {}
            
            async fetchMessage(_history: History): Promise<string[]> {
                return this.superThis.requestCompletion(this.modelParams);
            }
            
            dispose(): void {
                return;
            }
        }(this, modelParams);
    } 
}