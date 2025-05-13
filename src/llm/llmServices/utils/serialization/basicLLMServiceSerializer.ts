import { illegalState } from "../../../../utils/errors/throwErrors";
import { LLMService } from "../../llmService";
import { CorrespondingInputServiceParams } from "../../llmServiceIdentifier";
import { LLMServiceIdentifier } from "../../llmServiceIdentifier";
import { LLMServiceParams } from "../../llmServiceParams";
import { selectLLMServiceProvider } from "../../llmServiceProvider";
import { LLMServiceControlParams } from "../llmServiceControlParams";

import { LLMServiceSerializer } from "./llmServiceSerializer";
import { getShortName } from "./toLog";
import { toOneLineLogString } from "./toLog";

export function provideBasicSerializer(
    llmService: LLMService
): BasicLLMServiceSerializer {
    return new BasicLLMServiceSerializer(
        llmService.identifier ??
            illegalState(
                "`BasicLLMServiceSerializer` supports only services ",
                `with defined \`identifier\`, but got: ${llmService.toLogString(false)}`
            ),
        llmService.serviceSetup
    );
}

export class BasicLLMServiceSerializer extends LLMServiceSerializer {
    constructor(
        readonly serviceIdentifier: LLMServiceIdentifier,
        readonly serviceParams: CorrespondingInputServiceParams<LLMServiceIdentifier>
    ) {
        super();
    }

    protected readonly selfClass = BasicLLMServiceSerializer;

    static readonly serializationType = "basicSerializer";
    static {
        LLMServiceSerializer.registerSelfSerialization(
            this.serializationType,
            BasicLLMServiceSerializer
        );
    }

    constructService(controlParams: LLMServiceControlParams): LLMService {
        const serviceCtor = selectLLMServiceProvider(
            this.serviceIdentifier,
            this.serviceParams
        );
        return serviceCtor(controlParams);
    }

    toLogString(verbose: boolean): string {
        return toOneLineLogString(
            getShortName(this.serviceIdentifier),
            this.serviceParams,
            verbose
        );
    }

    serializeData(): BasicLLMServiceProviderSerializedData {
        return {
            service: this.serviceIdentifier,
            serviceParams: this.serviceParams,
        };
    }

    static deserialize(serializedProviderData: any): LLMServiceSerializer {
        // TODO: would be nice to validate data, at least somehow
        return new BasicLLMServiceSerializer(
            serializedProviderData.service,
            serializedProviderData.serviceParams
        );
    }
}

interface BasicLLMServiceProviderSerializedData {
    service: LLMServiceIdentifier;
    serviceParams?: LLMServiceParams;
}
