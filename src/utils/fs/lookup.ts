import { exec } from "child_process";
import { promisify } from "util";

const execAsync = promisify(exec);

/**
 * Runs `which` shell command to locate the `target` executable.
 * Returns `undefined` on failure.
 */
export async function locateExecutable(
    target: string
): Promise<string | undefined> {
    try {
        const { stdout } = await execAsync(`which ${target}`);
        return stdout.trim() || undefined;
    } catch (e) {
        return undefined;
    }
}
