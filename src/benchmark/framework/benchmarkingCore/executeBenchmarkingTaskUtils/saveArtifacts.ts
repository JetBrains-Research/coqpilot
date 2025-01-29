import { getErrorMessage } from "../../../../utils/errorsUtils";
import { toFormattedJsonString } from "../../../../utils/printers";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { BasicJsonSerialization } from "../../reportBuilders/basicJson/serialization";
import { BenchmarkingItem } from "../../structures/benchmarkingCore/benchmarkingItem";
import { BenchmarkingResult } from "../../structures/benchmarkingResults/benchmarkedItem";
import { buildSafeJsonFileName } from "../../utils/fileUtils/fileNameUtils";
import { writeToFile } from "../../utils/fileUtils/fs";
import { throwBenchmarkingError } from "../../utils/throwErrors";

export namespace ExecuteBenchmarkingTaskArtifactsUtils {
    export function saveInputTaskToFileOrThrow(
        benchmarkingItem: BenchmarkingItem,
        filePath: string
    ) {
        return saveToFileAndLogOrThrowError(
            toFormattedJsonString(
                BasicJsonSerialization.serializeBenchmarkingItem(
                    benchmarkingItem
                )
            ),
            filePath,
            "task final result",
            undefined
        );
    }

    export function buildRoundResultFileName(
        roundNumber: number,
        parentProofToFixId: number | undefined
    ): string {
        const parentId =
            parentProofToFixId === undefined
                ? `generate-proofs`
                : `fix-proof-${parentProofToFixId}`;
        return buildSafeJsonFileName(`round-${roundNumber}-${parentId}`);
    }

    export function saveRoundResultToFileOrThrow(
        roundResult: BenchmarkingResult,
        filePath: string
    ) {
        return saveToFileAndLogOrThrowError(
            toFormattedJsonString(
                BasicJsonSerialization.serializeBenchmarkingResultAsSingleRound(
                    roundResult
                )
            ),
            filePath,
            `round result`,
            undefined
        );
    }

    export function saveResultToFile(
        rootResult: BenchmarkingResult,
        filePath: string,
        itemLogger: BenchmarkingLogger
    ) {
        return saveToFileAndLogOrThrowError(
            toFormattedJsonString(
                BasicJsonSerialization.serializeBenchmarkingResultAsRoundsTree(
                    rootResult
                )
            ),
            filePath,
            "task final result",
            itemLogger
        );
    }

    /**
     * @param itemLogger if specified, error will be logged and swallowed; otherwise it will be thrown.
     */
    function saveToFileAndLogOrThrowError(
        text: string,
        filePath: string,
        fileDescription: string,
        itemLogger: BenchmarkingLogger | undefined
    ) {
        writeToFile(text, filePath, (e) => {
            const errorMessage = `Failed to save ${fileDescription} into ${filePath}`;
            const causeMessage = `Cause: ${getErrorMessage(e)}`;
            if (itemLogger === undefined) {
                throwBenchmarkingError(`${errorMessage}\n${causeMessage}`);
            } else {
                itemLogger
                    ?.asOneRecord()
                    .error(errorMessage)
                    .debug(causeMessage);
            }
        });
    }
}
