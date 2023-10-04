import * as cliProgress from 'cli-progress';

export class ProgressBar {
    private current: number | null = null;
    private total: number | null = null;
    private id: string | null = null;
    private onUpdate: (newCount: number) => void;
    private onInit: (total: number) => void;
    private onEnd: () => void;

    constructor(
        onUpdate: (newCount: number) => void, 
        onInit: (total: number) => void, 
        onEnd: () => void
    ) {
        this.onUpdate = onUpdate;
        this.onInit = onInit;
        this.onEnd = onEnd;
    }

    public get isInitialized(): boolean {
        return this.total !== null && this.current !== null;
    }

    public get identifier(): string | null {
        return this.id;
    }

    public initialize(total: number, id: string): void {
        this.current = 0;
        this.total = total;
        this.id = id;
        this.onInit(this.total);
    }

    public updateCount(newCount: number): void {
        this.onUpdate(newCount);
        if (this.total === null || this.current === null) {
            throw new Error("Progress bar is not initialized");
        }
        this.current = newCount;
    }

    public increaseCount(): void {
        if (this.total === null || this.current === null) {
            throw new Error("Progress bar is not initialized");
        }
        this.onUpdate(this.current);
        this.current += 1;
    }

    public finish(): void {
        if (this.total === null || this.current === null) {
            throw new Error("Progress bar is not initialized");
        }
        this.onEnd();
    }
}

export class CliProgressBar extends ProgressBar {
    private bar: cliProgress.SingleBar | undefined;

    constructor() {
        super(
            (newCount: number) => { 
                if (this.bar === undefined) {
                    throw new Error("Progress bar is not initialized");
                }
                this.bar.update(newCount);
            },
            (total: number) => { 
                this.bar = new cliProgress.SingleBar({}, cliProgress.Presets.shades_classic);
                this.bar.start(total, 0);
            },
            () => {
                if (this.bar === undefined) {
                    throw new Error("Progress bar is not initialized");
                }
                this.bar.stop();
            }
        );
    }
}