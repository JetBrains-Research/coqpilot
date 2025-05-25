import { expect } from "earl";

import { ProofProvider } from "../../../proofProviders/impl/proofProvider";
import { ResponseStatus } from "../../../proofProviders/impl/utils/generationsLogger/loggerRecord";

export interface ExpectedRecord {
    status: ResponseStatus;
    error?: Error;
}

export function expectLogs(
    expectedRecords: ExpectedRecord[],
    proofProvider: ProofProvider
) {
    const actualRecordsUnwrapped = proofProvider
        .readGenerationsLogs()
        .map((record) => {
            return {
                status: record.responseStatus,
                error: record.error,
            };
        });
    const expectedRecordsUnwrapped = expectedRecords.map((record) => {
        return {
            status: record.status,
            error: record.error
                ? {
                      typeName: record.error.name,
                      message: record.error.message,
                  }
                : undefined,
        };
    });
    expect(actualRecordsUnwrapped).toHaveLength(
        expectedRecordsUnwrapped.length
    );
    // if exact error is not expected, ignore it in the actual records
    for (let i = 0; i < expectedRecordsUnwrapped.length; i++) {
        const expected = expectedRecordsUnwrapped[i];
        const actual = actualRecordsUnwrapped[i];
        if (
            expected.status === "FAILURE" &&
            actual.status === "FAILURE" &&
            expected.error === undefined
        ) {
            actual.error = undefined;
        }
    }
    expect(actualRecordsUnwrapped).toEqual(expectedRecordsUnwrapped);
}
