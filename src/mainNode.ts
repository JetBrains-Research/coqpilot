import { ExtensionContext } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { Coqpilot, ClientFactoryType } from "./extension";

let extension: Coqpilot;

const cf: ClientFactoryType = (_context, clientOptions, wsConfig) => {
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

export async function activate(context: ExtensionContext): Promise<void> {
    const extension = await Coqpilot.init(context, cf);
    context.subscriptions.push(extension);
}
  
export function deactivate() {
    extension.deactivateCoqLSP();
}