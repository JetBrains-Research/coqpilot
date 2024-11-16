import { Uri } from "../../../../utils/uri";

export type SerializedUri = string;

export function serializeUri(uriObject: Uri): SerializedUri {
    return uriObject.uri;
}

export function deserializeUri(serializedUri: SerializedUri): Uri {
    return Uri.fromUriString(serializedUri);
}
