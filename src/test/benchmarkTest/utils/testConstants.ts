import { time, timeToMillis } from "../../../utils/time";

export namespace BenchmarkingTestsConstants {
    export const TEST_DATASET_NAME = ".test-sources";
    export const SIMPLE_TEST_TIMEOUT = timeToMillis(time(5, "minute"));
}
