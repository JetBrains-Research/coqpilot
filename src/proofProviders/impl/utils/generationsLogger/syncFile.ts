import * as fs from "fs";
import * as path from "path";

/**
 * Since `SyncFile` methods are not `async`,
 * they are expected to be effectively "synchronized".
 * This means that despite the concurrent nature of some parts of the system
 * (for example, completing several "admit"-s concurrently),
 * this class indeed provides a concurrent-safe way to work with a file.
 */
export class SyncFile {
    constructor(
        public readonly filePath: string,
        public readonly encoding: string = "utf-8"
    ) {}

    exists(): boolean {
        return fs.existsSync(this.filePath);
    }

    write(data: string) {
        fs.writeFileSync(
            this.filePath,
            data,
            this.encoding as fs.WriteFileOptions
        );
    }

    append(data: string) {
        fs.appendFileSync(
            this.filePath,
            data,
            this.encoding as fs.WriteFileOptions
        );
    }

    read(): string {
        return fs.readFileSync(this.filePath, this.encoding as BufferEncoding);
    }

    createReset() {
        fs.mkdirSync(path.dirname(this.filePath), { recursive: true });
        fs.writeFileSync(this.filePath, "");
    }

    delete() {
        fs.unlinkSync(this.filePath);
    }
}
