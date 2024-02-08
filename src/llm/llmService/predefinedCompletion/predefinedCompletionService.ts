import { 
    PredefinedCompletionModelParams,
    CompletionContext
} from '../modelParamsInterfaces';
import { LLMServiceInterface } from '../llmServiceInterface';

export class PredefinedCompletionService implements LLMServiceInterface {
    async requestCompletion(
        _completionContext: CompletionContext,
        params: PredefinedCompletionModelParams
    ): Promise<string[]> {
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

    dispose(): void {
        return;
    }
}