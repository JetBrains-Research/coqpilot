import { PlatformBuilder } from "@tsed/common";
import { PlatformExpress } from "@tsed/platform-express";
import { expect } from "earl";
import { Application } from "express";
import * as SuperTest from "supertest";

import { Server } from "../../agentServer/server";

import { serverRunRoot } from "./commonServerTestFunctions";

process.env.SERVER_RUN_ROOT = serverRunRoot;

// Once again, due to the vscode absurd dependency,
// these tests are all in one, as mocha's
// before/after hooks are not available.
suite("AgentServer: RestAPI HTTP test", async () => {
    async function getServer(): Promise<PlatformBuilder<Application>> {
        const platform = await PlatformExpress.bootstrap(Server, {
            logger: {
                level: "off",
            },
        });
        await platform.listen();
        return platform;
    }

    test("GET requests to /rest/", async () => {
        const server = await getServer();

        const request = SuperTest(server.callback());

        // GET /rest/document
        let response = await request.get("/rest/document").expect(200);
        expect(response.body.projectRoot).not.toBeNullish();
        expect(response.body.projectRoot).toEqual(serverRunRoot);

        // GET /rest/document/theorem-names
        response = await request
            .get("/rest/document/theorem-names")
            .query({ filePath: "small_document.v" })
            .expect(200);

        expect(response.body.theoremNames).not.toBeNullish();
        expect(response.body.theoremNames).toEqual(["test_thr", "test_thr1"]);

        // GET /rest/document/all-coq-files
        response = await request
            .get("/rest/document/all-coq-files")
            .expect(200);

        expect(response.body.coqFiles).not.toBeNullish();
        expect(response.body.coqFiles).toEqual([
            { name: "A.v", pathFromRoot: "coqProj/theories/A.v" },
            { name: "B.v", pathFromRoot: "coqProj/theories/B.v" },
            { name: "C.v", pathFromRoot: "coqProj/theories/C.v" },
            { name: "harder_than_auto.v", pathFromRoot: "harder_than_auto.v" },
            { name: "small_document.v", pathFromRoot: "small_document.v" },
            { name: "test_many_admits.v", pathFromRoot: "test_many_admits.v" },
            { name: "test_parse_proof.v", pathFromRoot: "test_parse_proof.v" },
        ]);

        // GET /rest/document/theorem
        response = await request
            .get("/rest/document/theorem")
            .query({ filePath: "small_document.v", theoremName: "test_thr" })
            .expect(200);

        expect(response.body.theoremStatement).not.toBeNullish();
        expect(response.body.theoremStatement).toEqual(
            "Theorem test_thr : forall n:nat, 0 + n = n."
        );

        response = await request
            .get("/rest/document/theorem")
            .query({ filePath: "small_document.v", theoremName: "not_exist" })
            .expect(400);

        await server.stop();
    });
});
