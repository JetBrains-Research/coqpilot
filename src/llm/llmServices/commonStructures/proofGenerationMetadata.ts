import { illegalState, invariantFailed } from "../../../utils/throwErrors";
import { LLMServiceError } from "../../llmServiceErrors";

import { AnalyzedChatHistory } from "./chat";
import { GeneratedRawContentItem } from "./generatedRawContent";
import { GenerationTokens } from "./generationTokens";
import {
    LLMServiceRequest,
    LLMServiceRequestFailed,
    LLMServiceRequestSucceeded,
} from "./llmServiceRequest";
import { ProofGenerationType } from "./proofGenerationType";

export interface SuccessfulProofGenerationMetadata
    extends ConfigurationMetadata,
        SuccessMetadata {}

export interface FailedProofGenerationMetadata
    extends ConfigurationMetadata,
        FailureMetadata {}

interface ConfigurationMetadata {
    proofGenerationType: ProofGenerationType;
    analyzedChat: AnalyzedChatHistory | undefined;
}

interface SuccessMetadata {
    generatedRawProofs: GeneratedRawContentItem[];
    tokensSpentInTotal: GenerationTokens;
}

interface FailureMetadata {
    llmServiceError: LLMServiceError;
}

// TODO: document, especially its invariant to be used only once
export class ProofGenerationMetadataHolder {
    private _configuration: ConfigurationMetadata | undefined = undefined;
    private _success: SuccessMetadata | undefined = undefined;
    private _failure: FailureMetadata | undefined = undefined;

    getSuccessfulProofGenerationMetadata(): SuccessfulProofGenerationMetadata {
        if (this._configuration === undefined) {
            this.throwOnConfigurationMetadataIsNotSet();
        }
        if (this._success === undefined) {
            if (this._failure !== undefined) {
                illegalState(
                    "success metadata is queried for the failed proof generation"
                );
            } else {
                illegalState(
                    "success metadata is queried before it has been set"
                );
            }
        }
        return {
            ...this._configuration,
            ...this._success,
        };
    }

    getFailedProofGenerationMetadata(): FailedProofGenerationMetadata {
        if (this._configuration === undefined) {
            this.throwOnConfigurationMetadataIsNotSet();
        }
        if (this._failure === undefined) {
            if (this._success !== undefined) {
                illegalState(
                    "failure metadata is queried for the successful proof generation"
                );
            } else {
                illegalState(
                    "failure metadata is queried before it has been set"
                );
            }
        }
        return {
            ...this._configuration,
            ...this._failure,
        };
    }

    setProofGenerationType(type: ProofGenerationType) {
        this.throwIfRepeatedSet(this._configuration, "proof generation type");
        this._configuration = {
            proofGenerationType: type,
            analyzedChat: undefined,
        };
    }

    updateWithBuiltRequest(builtRequest: LLMServiceRequest) {
        if (this._configuration === undefined) {
            invariantFailed(
                "`ProofGenerationMetadataHolder`",
                "analyzed chat is set before proof generation type has been"
            );
        }
        this.throwIfRepeatedSet(
            this._configuration.analyzedChat,
            "built request"
        );
        this._configuration.analyzedChat = builtRequest.analyzedChat;
    }

    setSuccessMetadata(requestSucceeded: LLMServiceRequestSucceeded) {
        this.throwIfRepeatedSet(this._success, "success metadata");
        this._success = {
            generatedRawProofs: requestSucceeded.generatedRawProofs,
            tokensSpentInTotal: requestSucceeded.tokensSpentInTotal,
        };
    }

    setFailureMetadata(requestFailed: LLMServiceRequestFailed) {
        this.throwIfRepeatedSet(this._failure, "failure metadata");
        this._failure = {
            llmServiceError: requestFailed.llmServiceError,
        };
    }

    private throwIfRepeatedSet(
        currentValue: any | undefined,
        propertyName: string
    ) {
        if (currentValue !== undefined) {
            illegalState(
                `\`ProofGenerationMetadata\` is updated with ${propertyName} more than once;\n`,
                "Possible reasone: the same `ProofGenerationMetadata` should not be used ",
                "more than for one proof generation"
            );
        }
    }

    private throwOnConfigurationMetadataIsNotSet(): never {
        invariantFailed(
            "`LLMService` proof generation",
            "metadata is queried before the configuration one has been set: ",
            "configuration metadata should be set in the very beggining ",
            "of the proof generation execution"
        );
    }
}
