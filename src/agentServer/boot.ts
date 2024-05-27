import { $log } from "@tsed/common";
import { PlatformExpress } from "@tsed/platform-express";

import { Server } from "./server";

export function run(): Promise<void> {
    return new Promise(async (_resolve, reject) => {
        try {
            $log.debug("Starting server...");
            const platform = await PlatformExpress.bootstrap(Server, {});
            await platform.listen();
        } catch (er) {
            $log.error(er);
            reject(er);
        }
    });
}
