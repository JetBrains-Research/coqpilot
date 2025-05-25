import { illegalState } from "../../../../utils/errors/throwErrors";
import { ProofProvider } from "../../proofProvider";
import { selectProofProviderConstructor } from "../../proofProviderConstructor";
import { CorrespondingInputProofProviderParams } from "../../proofProviderIdentifier";
import { ProofProviderIdentifier } from "../../proofProviderIdentifier";
import { getShortName } from "../../proofProviderIdentifier";
import { ProofProviderParams } from "../../proofProviderParams";
import { ProofProviderControlParams } from "../proofProviderControlParams";

import { ProofProviderSerializer } from "./proofProviderSerializer";
import { toOneLineLogString } from "./toLog";

export function provideBasicSerializer(
    proofProvider: ProofProvider
): BasicProofProviderSerializer {
    return new BasicProofProviderSerializer(
        proofProvider.identifier ??
            illegalState(
                "`BasicProofProviderSerializer` supports only proofProviders ",
                `with defined \`identifier\`, but got: ${proofProvider.toLogString(false)}`
            ),
        proofProvider.proofProviderSetup
    );
}

export class BasicProofProviderSerializer extends ProofProviderSerializer {
    constructor(
        readonly proofProviderIdentifier: ProofProviderIdentifier,
        readonly proofProviderParams: CorrespondingInputProofProviderParams<ProofProviderIdentifier>
    ) {
        super();
    }

    protected readonly selfClass = BasicProofProviderSerializer;

    static readonly serializationType = "basicSerializer";
    static {
        ProofProviderSerializer.registerSelfSerialization(
            this.serializationType,
            BasicProofProviderSerializer
        );
    }

    constructProofProvider(
        controlParams: ProofProviderControlParams
    ): ProofProvider {
        const proofProviderCtor = selectProofProviderConstructor(
            this.proofProviderIdentifier,
            this.proofProviderParams
        );
        return proofProviderCtor(controlParams);
    }

    toLogString(verbose: boolean): string {
        return toOneLineLogString(
            getShortName(this.proofProviderIdentifier),
            this.proofProviderParams,
            verbose
        );
    }

    serializeData(): BasicProofProviderConstructorSerializedData {
        return {
            proofProvider: this.proofProviderIdentifier,
            proofProviderParams: this.proofProviderParams,
        };
    }

    static deserialize(serializedProviderData: any): ProofProviderSerializer {
        // TODO: would be nice to validate data, at least somehow
        return new BasicProofProviderSerializer(
            serializedProviderData.proofProvider,
            serializedProviderData.proofProviderParams
        );
    }
}

interface BasicProofProviderConstructorSerializedData {
    proofProvider: ProofProviderIdentifier;
    proofProviderParams?: ProofProviderParams;
}
