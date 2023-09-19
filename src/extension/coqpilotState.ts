import { AutoQueue } from './taskQueue';
import { CoqpilotConfig } from './config';
import { Interactor } from '../coqLlmInteraction/interactor';
import { CoqPromptKShot } from '../coqLlmInteraction/coqLlmPrompt';
import { VsCodeProgressBar, VsCodeSpinningWheelProgressBar } from './vscodeProgressBar';
import { lspmodels } from 'coqlsp-client';

export class CoqpilotState {
    private queue: AutoQueue;
    private coqLlmInteractor: Interactor;
    private admittedTheorems: string[];

    get admitted(): string[] {
        return this.admittedTheorems;
    }

    private constructor(
        coqLlmInteractor: Interactor, 
        admittedTheorems: string[],
    ) {
        this.queue = new AutoQueue();
        this.coqLlmInteractor = coqLlmInteractor;
        this.admittedTheorems = admittedTheorems;
    }

    static async init(config: CoqpilotConfig): Promise<CoqpilotState> {
        const progressIndicatorPercentage = new VsCodeProgressBar();
        const progressIndicatorSpinningWheel = new VsCodeSpinningWheelProgressBar();
        const llmPrompt = await CoqPromptKShot.init(
            config.coqFilePath, config.coqFileRootDir, 
            config.maxNumberOfTokens, undefined, 
            progressIndicatorPercentage
        );
        const llmInterface = CoqpilotConfig.getLlm(config);
        const coqLlmInteractor = new Interactor(
            llmPrompt, 
            llmInterface, 
            progressIndicatorSpinningWheel,
            config.logAttempts,
            config.proofAttemsPerOneTheorem,
            config.logFolderPath
        ); 
        const admittedTheorems = llmPrompt.getAdmittedTheorems();

        return new CoqpilotState(coqLlmInteractor, admittedTheorems);
    }

    isTaskQueueEmpty(): boolean {
        return this.queue.size === 0;
    }

    async tryProveTheorem(thrName: string): Promise<string | undefined> {
        return this.queue.enqueue(async () => {
            const [thrStatement, proof] = await this.coqLlmInteractor.runCompleteProofGerenation(thrName);
            if (proof) {
                const proofText = `${thrStatement}\n${proof}`;
                return proofText;
            } else {
                return undefined;
            }
        });
    }

    async tryProveHole(thrName: string, holeIndex: number): Promise<string | undefined> {
        return this.queue.enqueue(async () => {
            const [thrStatement, proof] = await this.coqLlmInteractor.runHoleSubstitution(thrName, holeIndex);
            if (proof) {
                const proofText = `${thrStatement}\n${proof}`;
                return proofText;
            } else {
                return undefined;
            }
        });
    }

    getHolesNum(thrName: string): number {
        return this.coqLlmInteractor.getHolesNum(thrName);
    }

    getHoleApplyTactic(thrName: string, holeIndex: number): [string, lspmodels.Range] {
        return this.coqLlmInteractor.getAuxTheoremApplyTactic(thrName, holeIndex);
    }

    dispose() {
        this.coqLlmInteractor.stop();
    }
}