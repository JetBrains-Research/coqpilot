import { ExtensionContext } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { activateCoqLSP, ClientFactoryType, deactivateCoqLSP } from "./coqLspClient/client";

export function activate(context: ExtensionContext): void {
    const cf: ClientFactoryType = (_context, clientOptions, wsConfig) => {
        console.log("KKKKKK", wsConfig.args);
        const serverOptions: ServerOptions = {
            command: "coq-lsp",
            args: wsConfig.args,
        };
        return new LanguageClient(
            "coq-lsp",
            "Coq LSP Server",
            serverOptions,
            clientOptions
        );
    };
    return activateCoqLSP(context, cf);
}
  
export function deactivate() {
    return deactivateCoqLSP();
}