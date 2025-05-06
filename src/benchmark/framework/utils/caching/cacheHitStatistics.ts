// TODO: make a class with good-looking methods
export interface CacheHitStatistics {
    hitsNumber: number;
    missesNumber: number;
}

export function zeroRequestsStatistics(): CacheHitStatistics {
    return {
        hitsNumber: 0,
        missesNumber: 0,
    };
}

export function getCacheAccuracyLog(stats: CacheHitStatistics): string {
    const totalAttempts = stats.hitsNumber + stats.missesNumber;
    const accuracy = stats.hitsNumber / totalAttempts;
    return `${accuracy.toFixed(2)} (${stats.hitsNumber} / ${totalAttempts} cache hits)`;
}
