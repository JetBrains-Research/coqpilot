export interface LightweightWorkspaceRoot {
    /**
     * Relative to the project root.
     */
    relativeDirectoryPath: string;
    requiresNixEnvironment: boolean;
}
