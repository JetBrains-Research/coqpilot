class ProgressBar {
    private current: number | undefined;
    private total: number | undefined;
    private onUpdateCount: (arg0: number) => void;
    private onInit: (arg0: number) => void;
    private onEnd: () => void;

    getTotal(): number | undefined {
        return this.total;
    }
  
    constructor(onUpdateCount: (arg0: number) => void, onInit: (arg0: number) => void, onEnd: () => void) {
        this.onUpdateCount = onUpdateCount;
        this.onInit = onInit;
        this.onEnd = onEnd;
    }
  
    initialize(total: number) {
        this.current = 0;
        this.total = total;
        this.onInit(this.total);
    }
  
    updateCount(newCount: number) {
        if (this.total === undefined || this.current === undefined) {
            throw new Error("Progress bar is not initialized");
        }
        this.current = newCount;
        this.onUpdateCount(this.current);
    }

    finish() {
        if (this.total === undefined || this.current === undefined) {
            throw new Error("Progress bar is not initialized");  
        }
        this.onEnd();
    }
}