export type Without<A, B> = Pick<A, Exclude<keyof A, keyof B>>;
