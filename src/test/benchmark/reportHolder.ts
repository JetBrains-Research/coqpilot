import { JSONSchemaType } from "ajv";
import { ValidateFunction } from "ajv/dist/types";
import { existsSync, readFileSync, writeFileSync } from "fs";

import { AjvMode, buildAjv } from "../../utils/ajvErrorsHandling";

export interface TheoremProofResult {
    theoremName: string;
    filePath: string;
    modelId: string;
    generatedProof: string;
    chosenPremises: string[];
    generatedAtAttempt: number;
    group: string;
}

export type BenchmarkReport = Record<string, TheoremProofResult[]>;

export const theoremProofResultSchema: JSONSchemaType<TheoremProofResult> = {
    type: "object",
    properties: {
        modelId: { type: "string" },
        theoremName: { type: "string" },
        filePath: { type: "string" },
        generatedProof: { type: "string" },
        chosenPremises: { type: "array", items: { type: "string" } },
        generatedAtAttempt: { type: "number" },
        group: { type: "string" },
    },
    required: [
        "modelId",
        "theoremName",
        "filePath",
        "generatedProof",
        "chosenPremises",
        "generatedAtAttempt",
        "group",
    ],
    additionalProperties: false,
};

export class BenchmarkReportHolder {
    private readonly validate: ValidateFunction<TheoremProofResult>;
    private readonly groupOrder = ["A", "B", "C"];

    constructor(private readonly reportPath: string) {
        console.log("Report path: ", reportPath);
        if (!existsSync(reportPath)) {
            writeFileSync(reportPath, "{}");
        }

        const jsonSchemaValidator = buildAjv(AjvMode.RETURN_AFTER_FIRST_ERROR);
        this.validate = jsonSchemaValidator.compile(theoremProofResultSchema);
    }

    addProofResult(proofResult: TheoremProofResult) {
        const report = this.parseReport();
        if (!report[proofResult.theoremName]) {
            report[proofResult.theoremName] = [];
        }
        report[proofResult.theoremName].push(proofResult);
        writeFileSync(this.reportPath, JSON.stringify(report, null, 4));
    }

    generateMarkdown() {
        const report = this.parseReport();

        let markdownContent = "## Results\n\n";
        markdownContent +=
            "In the table below you can find the results of our experiments. For each of the theorems we show its group and the methods which proved the theorem during our experiments.\n\n";

        const header =
            "| Group | File | Theorem Name | Predefined tactic | OpenAI GPT-4 | OpenAI GPT-3.5 | LLaMA-2 13B Chat | Anthropic Claude |\n";
        const separator =
            "|-------|------|--------------|-------------------|--------------|----------------|------------------|------------------|\n";
        markdownContent += header + separator;

        const theoremLinks: Record<string, string> = {};

        for (const group of this.groupOrder) {
            for (const [theoremName, results] of Object.entries(report)) {
                if (results[0].group === group) {
                    const rowTemplate = {
                        group: "&#x2717;",
                        filePath: "&#x2717;",
                        theoremName: theoremName,
                        predefined: "&#x2717;",
                        gpt4: "&#x2717;",
                        gpt35: "&#x2717;",
                        llama2: "&#x2717;",
                        claude: "&#x2717;",
                    };

                    results.forEach((result) => {
                        rowTemplate.group = result.group;
                        rowTemplate.filePath = `[${result.filePath.split("/").pop()}](https://github.com/weakmemory/imm/tree/coq819/src/${result.filePath})`;

                        if (result.modelId === "OpenAI GPT-4") {
                            rowTemplate.gpt4 = `[&#x2713;](#${result.theoremName.toLowerCase()})`;
                        } else if (result.modelId === "OpenAI GPT-3.5") {
                            rowTemplate.gpt35 = `[&#x2713;](#${result.theoremName.toLowerCase()})`;
                        } else if (result.modelId === "LLaMA-2 13B Chat") {
                            rowTemplate.llama2 = `[&#x2713;](#${result.theoremName.toLowerCase()})`;
                        } else if (result.modelId === "Anthropic Claude") {
                            rowTemplate.claude = `[&#x2713;](#${result.theoremName.toLowerCase()})`;
                        }
                    });

                    markdownContent += `| ${rowTemplate.group} | ${rowTemplate.filePath} | \`${rowTemplate.theoremName}\` | ${rowTemplate.predefined} | ${rowTemplate.gpt4} | ${rowTemplate.gpt35} | ${rowTemplate.llama2} | ${rowTemplate.claude} |\n`;
                    theoremLinks[theoremName.toLowerCase()] = theoremName;
                }
            }
        }

        markdownContent += "\n## Generated Proofs\n\n";
        markdownContent +=
            "Here you can find the generated proofs for each of the proved theorems during the experiments.\n\n";

        this.groupOrder.forEach((group) => {
            markdownContent += `### Group ${group}\n\n`;

            for (const [theoremName, results] of Object.entries(report)) {
                if (results[0].group === group) {
                    markdownContent += `#### Theorem name: \n#### \`${theoremName}\`\n\n`;

                    results.forEach((result) => {
                        markdownContent += `#### ${result.modelId} Proof:\n\n\`\`\`\n${result.generatedProof}\n\`\`\`\n\n`;
                    });
                }
            }
        });

        writeFileSync(
            this.reportPath.replace(".json", ".md"),
            markdownContent,
            { encoding: "utf-8" }
        );
    }

    parseReport(): BenchmarkReport {
        const reportContent = JSON.parse(
            readFileSync(this.reportPath, { encoding: "utf-8" })
        );
        const report: BenchmarkReport = {};
        for (const [theoremName, proofResults] of Object.entries(
            reportContent
        )) {
            if (!Array.isArray(proofResults)) {
                console.error(
                    "Proof results for theorem ",
                    theoremName,
                    " are not an array"
                );
                continue;
            }

            const parsedProofResults = proofResults.map((proofResult: any) => {
                if (!this.validate(proofResult)) {
                    console.error(
                        "Failed to validate proof result: ",
                        this.validate.errors
                    );
                    return null;
                }
                return proofResult as TheoremProofResult;
            });

            report[theoremName] = parsedProofResults.filter(
                (proofResult) => proofResult !== null
            ) as TheoremProofResult[];
        }

        return report;
    }
}
