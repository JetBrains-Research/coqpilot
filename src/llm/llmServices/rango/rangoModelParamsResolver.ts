import { createDirectory } from "../../../utils/fs/directoryUtils";
import { exists, isAbsolutePath } from "../../../utils/fs/pathUtils";
import { createTmpDirectory } from "../../../utils/fs/tmpFs";
import { RangoUserModelParams } from "../../userModelParams";
import {
    RangoModelMode,
    RangoModelParams,
    rangoModelParamsSchema,
} from "../modelParams";
import { ValidationRules } from "../utils/paramsResolvers/builders";
import { DefaultNonChatBasedModelParamsResolver } from "../utils/paramsResolvers/kit/nonChatBasedModelParamsResolver";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class RangoModelParamsResolver
    extends DefaultNonChatBasedModelParamsResolver<
        RangoUserModelParams,
        RangoModelParams
    >
    implements ValidParamsResolverImpl<RangoUserModelParams, RangoModelParams>
{
    constructor() {
        super(rangoModelParamsSchema, "RangoModelParams");
    }

    readonly mode = this.resolveParam<RangoModelMode>("mode")
        .requiredToBeConfigured()
        .noValidationNeeded();

    readonly timeoutSeconds = this.resolveParam<number>("timeoutSeconds")
        .default((inputParams) => {
            switch (inputParams.mode) {
                case "local":
                case "remote":
                    return RangoValues.DEFAULT_MODEL_TIMEOUT_SECONDS;
                case "mockOpenAI":
                    return RangoValues.DEFAULT_MOCK_OPENAI_TIMEOUT_SECONDS;
            }
        })
        .validate(ValidationRules.bePositiveNumber, [
            (value, inputParams) =>
                !(
                    inputParams.mode === "mockOpenAI" &&
                    value > RangoValues.MAX_OPENAI_TIMEOUT_SECONDS
                ),
            [
                `be not greater than ${RangoValues.MAX_OPENAI_TIMEOUT_SECONDS} seconds in the \`mockOpenAI\` mode; `,
                "reason: prevent OpenAI API tokens being uncontrollably spent",
            ].join(""),
        ]);

    readonly localCheckpointPath = this.resolveParam<string>(
        "localCheckpointPath"
    )
        .override(
            (inputParams) =>
                inputParams.mode === "local"
                    ? inputParams.localCheckpointPath
                    : "",
            "is unused in any mode except the `local` one"
        )
        .default(() => RangoValues.DEFAULT_LOCAL_CHECKPOINT_PATH)
        .validateAtRuntimeOnly(); // since path could be a relative one, no checks for the actual path can be perfomed so far

    readonly mappedToRemotePort = this.resolveParam<number>(
        "mappedToRemotePort"
    )
        .override(
            (inputParams) =>
                inputParams.mode === "remote"
                    ? inputParams.mappedToRemotePort
                    : 0,
            "is unused in any mode except the `remote` one"
        )
        .default(() => RangoValues.DEFAULT_MAPPED_TO_REMOTE_PORT)
        .validate(ValidationRules.beValidPortNumber);

    readonly mockOpenAIApiKey = this.resolveParam<string>("mockOpenAIApiKey")
        .override(
            (inputParams) =>
                inputParams.mode === "mockOpenAI"
                    ? inputParams.mockOpenAIApiKey
                    : "",
            "is unused in any mode except the `mockOpenAI` one"
        )
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly enableWholeProjectDataPoints = this.resolveParam<boolean>(
        "enableWholeProjectDataPoints"
    )
        .default(() => RangoValues.DEFAULT_WHOLE_PROJECT_DATA_POINTS_ENABLED)
        .noValidationNeeded();

    readonly dataLocDirectoryPath = this.resolveParam<string>(
        "dataLocDirectoryPath"
    )
        .default(() =>
            createDirectory(
                true,
                createTmpDirectory({ unsafeCleanup: true }),
                "coqpilot-rango-request"
            )
        )
        .validate(
            [(value) => isAbsolutePath(value), "be an absolute path"],
            [(value) => exists(value), "exist"]
        );

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override(
            () => 1,
            `always equals to 1: Rango performs whole proof search by itself`
        )
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}

export namespace RangoValues {
    export const DEFAULT_MODEL_TIMEOUT_SECONDS = 600;
    export const DEFAULT_MOCK_OPENAI_TIMEOUT_SECONDS = 3;
    /**
     * Since in the `mockOpenAI` mode the `timeout` parameters
     * is the only one limiting the OpenAI proof generation attemps
     * (spending tokens), it is coerced to a maximum value for the sake of mistake.
     */
    export const MAX_OPENAI_TIMEOUT_SECONDS = 10;

    export const DEFAULT_LOCAL_CHECKPOINT_PATH =
        "models/deepseek-bm25-proof-tfidf-proj-thm-prem-final/checkpoint-54500";

    export const DEFAULT_MAPPED_TO_REMOTE_PORT = 5000;

    export const DEFAULT_WHOLE_PROJECT_DATA_POINTS_ENABLED = false;
}
