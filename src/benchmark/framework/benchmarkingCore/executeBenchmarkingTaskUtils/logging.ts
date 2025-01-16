import { illegalState } from "../../../../utils/throwErrors";
import { millisToString } from "../../../../utils/time";
import { BenchmarkingLogger } from "../../logging/benchmarkingLogger";
import { heavyCheckMark, heavyCrossMark } from "../../logging/specialSymbols";
import { BenchmarkingResult } from "../../structures/benchmarkingResults/benchmarkedItem";
import { benchmarkingInvariantFailed } from "../../utils/throwErrors";

export namespace ExecuteBenchmarkingTaskLoggingUtils {
    export function logRoundResult(
        roundResult: BenchmarkingResult,
        itemLogger: BenchmarkingLogger
    ) {
        const roundId =
            roundResult.parentProofToFixId === undefined
                ? "Root round of proof generation"
                : `Round ${roundResult.roundNumber} of fixing proof ${roundResult.parentProofToFixId}`;
        const asOneRecordLogs = itemLogger.asOneRecord();
        const logElapsedTime = () =>
            asOneRecordLogs.debug(
                `This round effective elapsed time: ${millisToString(roundResult.roundElapsedTime.totalMillis)}`
            );

        if (roundResult.isSuccessfullyFinishedRound()) {
            asOneRecordLogs.info(`${roundId} has been successfully finished:`);
            if (roundResult.isSuccessfulCompletion()) {
                asOneRecordLogs
                    .info(`Valid proof has been found ${heavyCheckMark}`)
                    .debug("First valid proof:")
                    .debug(roundResult.thisRoundValidProofs[0].asString);
            } else {
                asOneRecordLogs.debug(
                    `However, no valid proofs have been found ${heavyCrossMark}`
                );
            }
            const generatedProofsIds = roundResult.generatedProofs
                .map((proof) => `${proof.generatedProofId}`)
                .join(", ");
            asOneRecordLogs.debug(
                `Newly generated proofs id-s are: [${generatedProofsIds}]`
            );
            logElapsedTime();
        } else {
            const { failureType, causeMessage } = roundResult.failureMetadata;
            asOneRecordLogs
                .error(
                    `${roundId} has failed to finish: ${failureType}`,
                    "default"
                )
                .error(`Cause: ${causeMessage}`, "default");
            logElapsedTime();
            asOneRecordLogs.error(
                "This benchmarking task execution will be stopped"
            );
        }
    }

    export function logFinalResult(
        finalResult: BenchmarkingResult,
        itemLogger: BenchmarkingLogger
    ) {
        const asOneRecordLogs = itemLogger.asOneRecord();
        if (finalResult.isSuccessfulCompletion()) {
            const firstValidProof = finalResult.getAllValidProofs()[0];
            asOneRecordLogs
                .info(`Goal was succefully proven ${heavyCheckMark}`, "green")
                .debug(
                    `First valid proof was generated at round ${firstValidProof.proofObject.versionNumber}:`
                )
                .debug(`${firstValidProof.asString}`);
        } else {
            let logFailure: (message: string) => void;
            let failureMessage: string;
            let cause: string | undefined = undefined;
            if (finalResult.hasSuccessfullyFinished()) {
                logFailure = (message) => asOneRecordLogs.info(message, "red");
                failureMessage = "Valid proofs not found";
            } else {
                logFailure = (message) => asOneRecordLogs.error(message);

                const allFailedRounds =
                    finalResult.getAllFailedToFinishRounds();
                if (allFailedRounds.length > 1) {
                    benchmarkingInvariantFailed(
                        itemLogger,
                        "there are more than one failed rounds ",
                        "in the final benchmarking result mutliround tree; ",
                        "according to the implemented policy, the multiround benchmarking ",
                        "should be stopped as soon as the first failure occurred\nFailed nodes:\n",
                        allFailedRounds
                            .map((failedRound) =>
                                [
                                    `{ roundNumber: ${failedRound.roundNumber}; `,
                                    `parentProofToFixId: ${failedRound.parentProofToFixId}; `,
                                    `cause: ${failedRound.failureMetadata.failureType}, ${failedRound.failureMetadata.causeMessage} }`,
                                ].join("")
                            )
                            .join(",\n")
                    );
                }
                if (allFailedRounds.length === 0) {
                    illegalState(
                        "`finalResult.hasSuccessfullyFinished()` returned false,",
                        "but there are no failed rounds in its multiround subtree"
                    );
                }
                const firstFailedRound = allFailedRounds[0];
                switch (firstFailedRound.failureMetadata.failureType) {
                    case "`coq-lsp` timeout":
                        failureMessage = "Proof validation timeout";
                        break;
                    case "`CoqProofChecker` error":
                        failureMessage = "`CoqProofChecker` error";
                        break;
                }
                cause = firstFailedRound.failureMetadata.causeMessage;
            }

            logFailure(`${failureMessage} ${heavyCrossMark}`);
            if (cause !== undefined) {
                asOneRecordLogs.debug(`Cause: ${cause}`);
            }
        }

        asOneRecordLogs.debug(
            `Total effective elapsed time: ${millisToString(finalResult.getTotalElapsedTime().totalMillis)}`
        );
    }
}
