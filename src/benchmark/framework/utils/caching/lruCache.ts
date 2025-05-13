import { Mutex } from "async-mutex";

import {
    lastElement,
    printHeadTailItems,
    removeElementAndReturn,
} from "../../../../utils/collectionUtils/listUtils";
import { buildErrorCompleteLog } from "../../../../utils/errors/errorsUtils";
import {
    illegalState,
    invariantFailed,
} from "../../../../utils/errors/throwErrors";

import {
    CacheHitStatistics,
    getCacheAccuracyLog,
    zeroRequestsStatistics,
} from "./cacheHitStatistics";

export interface DisposableItem {
    dispose(): Promise<void>;
}

// TODO: cover with tests
export class AsyncLRUCache<ItemType extends DisposableItem> {
    private readonly keyToItem: Map<string, ItemType> = new Map();

    // 0th element - accessed least recent
    // last element - accessed most recently
    private readonly rangedByLastAccessKeys: string[] = [];

    private readonly stats: CacheHitStatistics = zeroRequestsStatistics();

    private mutex: Mutex = new Mutex();

    constructor(
        private readonly cacheSize: number,
        private readonly onLog: (message: string) => void = () => {}
    ) {}

    async getItemByKey(
        key: string,
        itemBuilder: () => Promise<ItemType>
    ): Promise<ItemType> {
        return await this.mutex.runExclusive(() =>
            this.getItemByKeyUnsafe(key, itemBuilder)
        );
    }

    async removeItemByKey(key: string, throwOnMissingKey: boolean) {
        return await this.mutex.runExclusive(() =>
            this.removeItemByKeyUnsafe(key, throwOnMissingKey)
        );
    }

    async dispose() {
        return await this.mutex.runExclusive(async () => {
            this.onLog("Dispose cache");
            const keys = Array.from(this.keyToItem.keys());
            for (const key of keys) {
                await this.removeItemByKeyUnsafe(key, true);
            }
        });
    }

    private async getItemByKeyUnsafe(
        key: string,
        itemBuilder: () => Promise<ItemType>
    ): Promise<ItemType> {
        const logGet = (message: string) => {
            this.onLog(
                `Get item by key "${key}": ${message}\n${this.getCurrentAccuracyLog()}`
            );
        };
        const presentItem = this.keyToItem.get(key);
        if (presentItem === undefined) {
            this.stats.missesNumber += 1;
            logGet(`no such item, it will be created`);
            return this.addToCacheUnsafe(key, itemBuilder);
        } else {
            this.stats.hitsNumber += 1;
            logGet("item is present, its last access will be updated");
            this.updateAsMostRecentAccessUnsafe(key);
            return presentItem;
        }
    }

    private async removeItemByKeyUnsafe(
        key: string,
        throwOnMissingKey: boolean
    ) {
        const removedAtIndex = removeElementAndReturn(
            this.rangedByLastAccessKeys,
            key
        );
        if (removedAtIndex === undefined) {
            if (throwOnMissingKey) {
                illegalState(
                    `LRU Cache error: no key "${key}" to remove found in ranged list`
                );
            } else {
                return;
            }
        }
        const itemToDispose =
            this.keyToItem.get(key) ??
            illegalState(
                `LRU Cache error: no item for the key "${key}" to remove`
            );
        this.keyToItem.delete(key);
        try {
            await itemToDispose.dispose();
        } catch (e) {
            this.onLog(
                `Error occurred during disposal of the item for the key "${key}": ${buildErrorCompleteLog(e)}`
            );
        }
        this.onLog(`Removed item by key "${key}"`);
    }

    private async addToCacheUnsafe(
        key: string,
        itemBuilder: () => Promise<ItemType>
    ): Promise<ItemType> {
        const newItem = await itemBuilder();
        this.keyToItem.set(key, newItem);

        if (this.rangedByLastAccessKeys.length === this.cacheSize) {
            const keyToRemove =
                lastElement(this.rangedByLastAccessKeys) ??
                illegalState(
                    "`LRUCache.cacheSize` is zero, but it must be positive"
                );
            this.onLog(
                `Add item by key "${key}": cache is full (${this.getCacheOccupacyLog()}), item with key "${keyToRemove}" will be removed`
            );
            await this.removeItemByKeyUnsafe(keyToRemove, true);
        } else {
            this.onLog(
                `Add item by key "${key}": cache is not full (${this.getCacheOccupacyLog()}), no item removed`
            );
        }
        this.rangedByLastAccessKeys.push(key);
        this.onLog(
            `Added item with key "${key}": cache occupacy is ${this.getCacheOccupacyLog()}`
        );

        return newItem;
    }

    private updateAsMostRecentAccessUnsafe(key: string) {
        const index = this.rangedByLastAccessKeys.indexOf(key);
        if (index === -1) {
            invariantFailed(
                "LRU Cache internal",
                "`updateAsMostRecentAccess` was called on a key not present in the ranged list; ",
                `key to update: ${key}, ranged keys: [${this.rangedByLastAccessKeys.join(", ")}]`
            );
        }
        this.rangedByLastAccessKeys.splice(index, 1);
        this.rangedByLastAccessKeys.push(key);
        this.onLog(
            `Updated last access of item with key "${key}": ${this.getRangedKeysViewLog()}`
        );
    }

    private getCacheOccupacyLog(): string {
        return `${this.rangedByLastAccessKeys.length} / ${this.cacheSize}`;
    }

    private getCurrentAccuracyLog(): string {
        return `Current accuracy: ${getCacheAccuracyLog(this.stats)}`;
    }

    private getRangedKeysViewLog(): string {
        const keysView = printHeadTailItems(
            2,
            2,
            this.rangedByLastAccessKeys,
            (key) => key
        );
        return `from latest to most recent accessed: [${keysView}]`;
    }
}
