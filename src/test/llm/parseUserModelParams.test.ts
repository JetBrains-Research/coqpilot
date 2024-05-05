import Ajv, { JSONSchemaType } from "ajv";
import { expect } from "earl";

import {
    grazieUserModelParamsSchema,
    lmStudioUserModelParamsSchema,
    openAiUserModelParamsSchema,
    predefinedProofsUserModelParamsSchema,
    userModelParamsSchema,
    userMultiroundProfileSchema,
} from "../../llm/userModelParams";

suite("Parse UserModelParams from JSON test", () => {
    const jsonSchemaValidator = new Ajv();

    function validateJSON<T>(
        json: any,
        targetClassSchema: JSONSchemaType<T>,
        expectedToBeValidJSON: boolean
    ) {
        const validate = jsonSchemaValidator.compile(targetClassSchema);
        expect(validate(json as T)).toEqual(expectedToBeValidJSON);
    }

    function isValidJSON<T>(json: any, targetClassSchema: JSONSchemaType<T>) {
        return validateJSON(json, targetClassSchema, true);
    }

    function isInvalidJSON<T>(json: any, targetClassSchema: JSONSchemaType<T>) {
        return validateJSON(json, targetClassSchema, false);
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
    };
    const validPredefinedProofsUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        tactics: ["auto.", "auto. intro."],
    };
    const validLMStudioUserModelParamsComplete = {
        ...validUserModelParamsCompelete,
        temperature: 36.6,
        port: 555,
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
        isInvalidJSON(invalidWrongTypeProp, userMultiroundProfileSchema);
        const invalidAdditionalProp = {
            ...validMultiroundProfileComplete,
            something: "something",
        };
        isInvalidJSON(invalidAdditionalProp, userMultiroundProfileSchema);
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
        isInvalidJSON(invalidNoModelId, userModelParamsSchema);
        const invalidWrongTypeProp = {
            ...validMultiroundProfileComplete,
            tokensLimit: "no limits",
        };
        isInvalidJSON(invalidWrongTypeProp, userMultiroundProfileSchema);
        const invalidAdditionalProp = {
            ...validUserModelParamsCompelete,
            something: "something",
        };
        isInvalidJSON(invalidAdditionalProp, userMultiroundProfileSchema);
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

    test("Validate `PredefinedProofsUserModelParams`", () => {
        isValidJSON(
            validPredefinedProofsUserModelParamsComplete,
            predefinedProofsUserModelParamsSchema
        );
    });

    test("Validate `LMStudioUserModelParams`", () => {
        isValidJSON(
            validLMStudioUserModelParamsComplete,
            lmStudioUserModelParamsSchema
        );
    });
});
