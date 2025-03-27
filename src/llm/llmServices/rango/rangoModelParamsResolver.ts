import { MockRangoUserModelParams } from "../../userModelParams";
import {
    MockRangoModelParams,
    MultiroundProfile,
    mockRangoModelParamsSchema,
} from "../modelParams";
import { BasicModelParamsResolver } from "../utils/paramsResolvers/basicModelParamsResolvers";
import { ValidationRules } from "../utils/paramsResolvers/builders";
import { ValidParamsResolverImpl } from "../utils/paramsResolvers/paramsResolverImpl";

export class RangoModelParamsResolver
    extends BasicModelParamsResolver<
        MockRangoUserModelParams,
        MockRangoModelParams
    >
    implements
        ValidParamsResolverImpl<MockRangoUserModelParams, MockRangoModelParams>
{
    constructor() {
        super(mockRangoModelParamsSchema, "MockRangoModelParams");
    }

    readonly openAiApiKey = this.resolveParam<string>("openAiApiKey")
        .requiredToBeConfigured()
        .validateAtRuntimeOnly();

    readonly timeoutSeconds = this.resolveParam<number>("timeoutSeconds")
        .default(() => defaultRangoTimeoutSeconds)
        .validate(ValidationRules.bePositiveNumber);

    readonly systemPrompt = this.resolveParam<string>(
        "systemPrompt"
    ).overrideWithMock(() => "");

    readonly maxTokensToGenerate = this.resolveParam<number>(
        "maxTokensToGenerate"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly tokensLimit = this.resolveParam<number>(
        "tokensLimit"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly maxContextTheoremsNumber = this.resolveParam<number>(
        "maxContextTheoremsNumber"
    ).overrideWithMock(() => Number.MAX_SAFE_INTEGER);

    readonly multiroundProfile = this.resolveParam<MultiroundProfile>(
        "multiroundProfile"
    ).overrideWithMock(() => {
        return {
            maxRoundsNumber: 1,
            defaultProofFixChoices: 0,
            proofFixPrompt: "",
            maxPreviousProofVersionsNumber: 0,
        };
    });

    readonly defaultChoices = this.resolveParam<number>("choices")
        .override(
            () => 1,
            `always equals to 1: Rango performs whole proof search by itself`
        )
        .requiredToBeConfigured()
        .validate(ValidationRules.bePositiveNumber);
}

export const defaultRangoTimeoutSeconds = 3;
