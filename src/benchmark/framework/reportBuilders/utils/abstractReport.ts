import { getErrorMessage } from "../../../../utils/errors/errorsUtils";
import {
    createFileWithParentDirectories,
    writeToFile,
} from "../../../../utils/fs/fileUtils";
import { resolveAsAbsoluteOrRootRelativePath } from "../../../../utils/fs/rootResolvers";

import { reportBuilderFailed } from "./errors";

export abstract class AbstractReport<MarkdownOptions, LatexOptions> {
    protected abstract toMarkdownString(options: MarkdownOptions): string;
    protected abstract toLatexString(options: LatexOptions): string;

    protected abstract resolveMarkdownOptions(
        inputOptions: Partial<MarkdownOptions>
    ): MarkdownOptions;
    protected abstract resolveLatexOptions(
        inputOptions: Partial<LatexOptions>
    ): LatexOptions;

    toMarkdown(
        outputFilePath?: string,
        options: Partial<MarkdownOptions> = {}
    ): string {
        const resolvedOptions = this.resolveMarkdownOptions(options);
        const content = this.toMarkdownString(resolvedOptions);
        return AbstractReport.outputContent(content, outputFilePath);
    }

    toLatex(
        outputFilePath?: string,
        options: Partial<LatexOptions> = {}
    ): string {
        const resolvedOptions = this.resolveLatexOptions(options);
        const content = this.toLatexString(resolvedOptions);
        return AbstractReport.outputContent(content, outputFilePath);
    }

    static outputContent(
        content: string,
        outputFilePath: string | undefined
    ): string {
        if (outputFilePath === undefined) {
            return content;
        }
        const resolvedFilePath = createFileWithParentDirectories(
            "throw",
            resolveAsAbsoluteOrRootRelativePath(outputFilePath)
        );
        writeToFile(content, resolvedFilePath, (err) =>
            reportBuilderFailed(
                `failed to save content to file ${resolvedFilePath}, `,
                `cause: ${getErrorMessage(err)}`
            )
        );
        return resolvedFilePath;
    }
}
