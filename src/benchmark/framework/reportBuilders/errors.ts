export class ReportBuilderError extends Error {
    constructor(message: string) {
        super(`Failed to build benchmarking report: ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
        this.name = "ReportBuilderError";
    }
}

export function throwReportBuilderError(...errorMessage: string[]): never {
    throw new ReportBuilderError(errorMessage.join(""));
}
