import * as fs from "fs";

export function getThisPathStats(inputPath: string): fs.Stats {
    return fs.lstatSync(inputPath);
}

export function getPathStats(inputPath: string): fs.Stats {
    return fs.statSync(inputPath);
}
