import { ConfigurationTarget, Uri, commands, workspace } from "vscode";

import { PLUGIN_ID } from "../../extension/utils/pluginId";
import { delay } from "../../utils/async/delay";
import { time, timeToMillis } from "../../utils/time";
import { resolveResourcesDir } from "../commonTestFunctions/pathsResolver";

import { TextDocumentWrapper } from "./documentUtils";

suite("Test CoqPilot Extension", () => {
    test("Smoke test: prove project theorem with `auto.`", async () => {
        const [filePath, workspaceRootPath] = resolveResourcesDir(
            ["coqProj", "theories", "C.v"],
            ["coqProj"]
        );
        const interactionDelayMillis = 1_000;

        workspace.updateWorkspaceFolders(
            0,
            workspace.workspaceFolders?.length ?? 0,
            { uri: Uri.file(workspaceRootPath) }
        );
        await delay(interactionDelayMillis);
        try {
            const targetDoc = await TextDocumentWrapper.create(filePath);
            await delay(interactionDelayMillis);

            targetDoc.checkDocumentContains("admit.");

            await workspace
                .getConfiguration("coqpilot")
                .update(
                    "openAiModelsParameters",
                    [],
                    ConfigurationTarget.Workspace
                );
            await workspace.getConfiguration("coqpilot").update(
                "predefinedProofsModelsParameters",
                [
                    {
                        modelId: "predefined-auto",
                        tactics: ["auto."],
                    },
                ],
                ConfigurationTarget.Workspace
            );
            await delay(interactionDelayMillis);

            await commands.executeCommand(
                `${PLUGIN_ID}.perform_completion_for_all_admits`
            );
            await delay(interactionDelayMillis);

            targetDoc.checkDocumentContains("auto.");

            await commands.executeCommand("undo");
            await commands.executeCommand("undo");
            await delay(interactionDelayMillis);

            targetDoc.checkDocumentContains("admit.");
        } finally {
            await commands.executeCommand("workbench.action.closeAllEditors");
        }
    }).timeout(timeToMillis(time(30, "second")));
});
