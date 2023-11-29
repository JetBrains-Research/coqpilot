import { CoqLspClient } from '../../coqLspClient/coqLspClient';
import { StatusBarButton, StatusBarState } from '../../editor/enableButton';
import { workspace } from 'vscode';
import * as assert from 'assert';
import { CoqpilotConfig, CoqpilotConfigWrapper } from "../../extension/config";
import { updateCoqpilotConfig } from "../common";

suite('CoqLspClient tests', () => {
    test('coq-lsp correctly modifying ui', async () => {
        const statusItem = new StatusBarButton();
        const wsConfig = workspace.getConfiguration("coqpilot");
        const extensionConfig = new CoqpilotConfigWrapper(
            updateCoqpilotConfig(CoqpilotConfig.create(wsConfig)!), false
        );
        console.log("EXTCONFIG", extensionConfig);
        const client = new CoqLspClient(statusItem, wsConfig, extensionConfig);
        
        assert.strictEqual(statusItem.runStatus, StatusBarState.Activating);
        await client.start();
        assert.strictEqual(statusItem.runStatus, StatusBarState.Running);
        assert.strictEqual(client.isRunning(), true);
    });
});