import {
    PredefinedProofsModelParams,
    ProofGenerationContext,
} from "../modelParamsInterfaces";
import { LLMServiceInterface } from "../llmServiceInterface";

export class PredefinedProofsService implements LLMServiceInterface {
    async generateProof(
        _proofGenerationContext: ProofGenerationContext,
        params: PredefinedProofsModelParams
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
