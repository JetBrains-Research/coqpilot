export async function delay(
    millis: number,
    abortSignal: AbortSignal | undefined = undefined
) {
    return new Promise((resolve, reject) => {
        const timeoutId = setTimeout(resolve, millis);
        abortSignal?.addEventListener("abort", () => {
            clearTimeout(timeoutId);
            reject(abortSignal.reason);
        });
    });
}
