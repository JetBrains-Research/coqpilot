import { SerializedProofProvider } from "../../../../../proofProviders/impl/utils/serialization/serializedProofProvider";

import { InputBenchmarkingModelParams } from "../inputBenchmarkingModelParams";

export interface LightweightInputModelParams
    extends InputBenchmarkingModelParams.Params {
    serializedProofProvider: SerializedProofProvider;
}
