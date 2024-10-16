export class AdditionalFileImport {
    constructor(private readonly importString: string) {}

    get(): string {
        return this.importString;
    }

    static unwrapper(): AdditionalFileImport {
        return new AdditionalFileImport(`Set Printing All.`);
    }

    static tactician(): AdditionalFileImport {
        return new AdditionalFileImport(`From Tactician Require Import Ltac1.`);
    }

    static coqHammer(): AdditionalFileImport {
        return new AdditionalFileImport(`From Hammer Require Import Hammer.`);
    }
}
