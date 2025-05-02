import { Uri } from "../../../../utils/structures/uri";

export type SerializedUri = string;

export function serializeUri(uriObject: Uri): SerializedUri {
    return uriObject.uri;
}

export function deserializeUri(serializedUri: SerializedUri): Uri {
    return Uri.fromUriString(serializedUri);
}
