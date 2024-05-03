export async function delay(millis: number) {
    return new Promise((resolve) => setTimeout(resolve, millis));
}
