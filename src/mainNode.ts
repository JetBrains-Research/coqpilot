import { ExtensionContext, commands } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { Coqpilot, ClientFactoryType } from "./extension";
import { StatusBarButton } from "./editor/enableButton";

let extension: Coqpilot | undefined;
let statusItem: StatusBarButton;

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

// async function togglePlugin(context: ExtensionContext) {
//     if (statusItem.isRunning) {
//         console.log("Stopping Extension");
//         extension.deactivateCoqLSP();
//         extension.dispose();
//         statusItem.updateClientStatus(false);
//         extension = undefined;
//     } else {
//         console.log("Starting Extension");
//         // Clear subscriptions
//         context.subscriptions.forEach((sub) => {
//             sub.dispose();
//         });
//         for (let i = context.subscriptions.length; i > 0; i--) {
//             context.subscriptions.pop();
//         }

//         // Clear registered commands
//         commands.getCommands(true).then((commands) => {
//             commands.forEach((command) => {
//                 commands.unregisterCommand(command);
//             });
//         });

//         extension = await Coqpilot.init(context, cf, statusItem);
//         context.subscriptions.push(extension);
//     }
// }

export async function activate(context: ExtensionContext): Promise<void> {
    extension = await Coqpilot.init(context, cf);
    context.subscriptions.push(extension);

    // let desposableReload = commands.registerCommand('coqpilot.toggle', async () => {
    //     console.log("Toggle Extension");
    //     await togglePlugin(context);
    // });

    // context.subscriptions.push(desposableReload);
}
  
export function deactivate() {
    extension.deactivateCoqLSP();
}