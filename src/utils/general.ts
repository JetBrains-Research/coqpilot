export const capitalize = (str: string = "", lowerRest = false): string =>
    str.slice(0, 1).toUpperCase() + (lowerRest ? str.slice(1).toLowerCase() : str.slice(1));