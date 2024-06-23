export type ResolveType<T> = (value: T | PromiseLike<T>) => void;

export type RejectType = (reason?: any) => void;

export interface PromiseExecutor<T> {
    resolve: ResolveType<T>;
    reject: RejectType;
}
