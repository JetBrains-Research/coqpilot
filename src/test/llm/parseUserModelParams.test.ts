import { JSONSchemaType } from "ajv";
import { expect } from "earl";

import {
    deepSeekUserModelParamsSchema,
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
    userModelParamsSchema,
    userMultiroundProfileSchema,
} from "../../llm/userModelParams";

import { AjvMode, buildAjv } from "../../utils/ajvErrorsHandling";

suite("Parse `UserModelParams` from JSON test", () => {
    const jsonSchemaValidator = buildAjv(AjvMode.COLLECT_ALL_ERRORS);

    function validateJSON<T>(
        json: any,
        targetClassSchema: JSONSchemaType<T>,
        expectedToBeValidJSON: boolean,
        expectedErrorKeys?: string[]
    ) {
        const validate = jsonSchemaValidator.compile(targetClassSchema);
        expect(validate(json as T)).toEqual(expectedToBeValidJSON);
        if (expectedErrorKeys !== undefined) {
            expect(validate.errors).not.toBeNullish();
            expect(
                new Set(validate.errors!.map((error) => error.keyword))
            ).toEqual(new Set(expectedErrorKeys));
        }
    }

    function isValidJSON<T>(json: any, targetClassSchema: JSONSchemaType<T>) {
        return validateJSON(json, targetClassSchema, true);
    }

    function isInvalidJSON<T>(
        json: any,
        targetClassSchema: JSONSchemaType<T>,
        ...expectedErrorKeys: string[]
    ) {
        return validateJSON(json, targetClassSchema, false, expectedErrorKeys);
    }

    const validMultiroundProfileComplete = {
        maxRoundsNumber: 5,
        proofFixChoices: 1,
        proofFixPrompt: "fix me",
    };

    const validUserModelParamsCompelete = {
        modelId: "unique model id",
        choices: 30,
        systemPrompt: "generate proof",
        maxTokensToGenerate: 100,
        tokensLimit: 2000,
        multiroundProfile: validMultiroundProfileComplete,
    };

    const validPredefinedProofsUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        tactics: ["auto.", "auto. intro."],
    };
    const validOpenAiUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        modelName: "gpt-model",
        temperature: 36.6,
        apiKey: "api-key",
    };
    const validGrazieUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        modelName: "gpt-model",
        apiKey: "api-key",
        authType: "stgn",
    };
    const validLMStudioUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        temperature: 36.6,
        port: 555,
    };
    const validDeepSeekUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        modelName: "deepseek-chat",
        temperature: 36.6,
        apiKey: "api-key",
    };

    test("Validate `UserMultiroundProfile`", () => {
        isValidJSON(
            validMultiroundProfileComplete,
            userMultiroundProfileSchema
        );
        const validUndefinedProp = {
            maxRoundsNumber: 5,
            proofFixChoices: 1,
            proofFixPrompt: undefined,
        };
        isValidJSON(validUndefinedProp, userMultiroundProfileSchema);
        const validEmpty = {};
        isValidJSON(validEmpty, userMultiroundProfileSchema);

        const invalidWrongTypeProp = {
            ...validMultiroundProfileComplete,
            proofFixPrompt: 0,
        };
        isInvalidJSON(
            invalidWrongTypeProp,
            userMultiroundProfileSchema,
            "type"
        );

        const invalidAdditionalProp = {
            ...validMultiroundProfileComplete,
            something: "something",
        };
        isInvalidJSON(
            invalidAdditionalProp,
            userMultiroundProfileSchema,
            "additionalProperties"
        );
    });

    test("Validate `UserModelParams`", () => {
        isValidJSON(validUserModelParamsCompelete, userModelParamsSchema);
        const validOnlyModelId = {
            modelId: "the only id",
        };
        isValidJSON(validOnlyModelId, userModelParamsSchema);

        const invalidNoModelId = {
            choices: 30,
            systemPrompt: "let's generate",
        };
        isInvalidJSON(invalidNoModelId, userModelParamsSchema, "required");

        const invalidWrongTypeProp = {
            ...validUserModelParamsCompelete,
            tokensLimit: "no limits",
        };
        isInvalidJSON(invalidWrongTypeProp, userModelParamsSchema, "type");

        const invalidAdditionalProp = {
            ...validUserModelParamsCompelete,
            something: "something",
        };
        isInvalidJSON(
            invalidAdditionalProp,
            userModelParamsSchema,
            "additionalProperties"
        );
    });

    test("Validate `PredefinedProofsUserModelParams`", () => {
        isValidJSON(
            validPredefinedProofsUserModelParamsComplete,
            predefinedProofsUserModelParamsSchema
        );
    });

    test("Validate `OpenAiUserModelParams`", () => {
        isValidJSON(
            validOpenAiUserModelParamsComplete,
            openAiUserModelParamsSchema
        );
    });

    test("Validate `GrazieUserModelParams`", () => {
        isValidJSON(
            validGrazieUserModelParamsComplete,
            grazieUserModelParamsSchema
        );
    });

    test("Validate `LMStudioUserModelParams`", () => {
        isValidJSON(
            validLMStudioUserModelParamsComplete,
            lmStudioUserModelParamsSchema
        );
    });

    test("Validate `DeepSeekUserModelParams`", () => {
        isValidJSON(
            validDeepSeekUserModelParamsComplete,
            deepSeekUserModelParamsSchema
        );
    });
});
