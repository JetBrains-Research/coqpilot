/**
 * A decorator that logs the execution time of a method.
 * Execution time is logged into console in milliseconds.
 *
 * (Note: typescript supports decorators only for class methods).
 */
export function logExecutionTime(
    _target: any,
    propertyKey: string,
    descriptor: PropertyDescriptor
) {
    const originalMethod = descriptor.value;

    descriptor.value = function (this: any, ...args: any[]) {
        const start = performance.now();

        const result = originalMethod.apply(this, args);

        const logTime = (duration: number) => {
            console.log(
                `${propertyKey} took ${duration.toFixed(2)}ms to execute`
            );
        };

        if (result && typeof result.then === "function") {
            return result
                .then((res: any) => {
                    const duration = performance.now() - start;
                    logTime(duration);
                    return res;
                })
                .catch((err: any) => {
                    const duration = performance.now() - start;
                    logTime(duration);
                    throw err;
                });
        } else {
            const duration = performance.now() - start;
            logTime(duration);
            return result;
        }
    };

    return descriptor;
}
