import * as tmp from "tmp";

/**
 * Creating temporary files in the system's default tmp directory may fail
 * when CoqPilot is run with a Nix environment and an incorrect `coq-lsp` path.
 * Explicitly setting the tmp directory to `/tmp` somehow resolves this issue.
 */
const DEFAULT_TMP_DIR = "/tmp";

// TODO: implement and use context functions instead to free resources faster

export function createTmpDirectory(options?: tmp.DirOptions) {
    return tmp.dirSync({ tmpdir: DEFAULT_TMP_DIR, ...options }).name;
}

export function createTmpFile(options?: tmp.FileOptions) {
    return tmp.fileSync({ tmpdir: DEFAULT_TMP_DIR, ...options }).name;
}
