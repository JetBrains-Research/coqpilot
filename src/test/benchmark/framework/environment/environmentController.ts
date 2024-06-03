import { stringifyAnyValue } from "../../../../utils/printers";

// TODO: add mutex
export class EnvironmentController {
    private currentWorkspacePath = process.cwd();

    async withNixEnvironment<T>(
        workspacePath: string,
        block: () => Promise<T>
    ): Promise<T> {
        // TODO: enter nix shell
        const previousWorkspacePath = this.currentWorkspacePath;
        const failureCause =
            this.changeDirectoryOrReportFailureCause(workspacePath);
        if (failureCause !== undefined) {
            throw Error(failureCause);
        }
        this.currentWorkspacePath = workspacePath;
        try {
            return await block();
        } finally {
            this.currentWorkspacePath = previousWorkspacePath;
            const failureCause = this.changeDirectoryOrReportFailureCause(
                this.currentWorkspacePath
            );
            if (failureCause !== undefined) {
                throw Error(
                    `environment controller got in invalid state: ${failureCause}`
                );
            }
        }
    }

    private enterNixShell(workspacePath: string) {
        // TODO: unfortunately, this could be done only by spawining a child process
    }

    private changeDirectoryOrReportFailureCause(
        newDirPath: string
    ): string | undefined {
        try {
            process.chdir(newDirPath);
            return undefined;
        } catch (e) {
            const error = e as Error;
            return error !== null ? error.message : stringifyAnyValue(error);
        }
    }
}
