import typescriptEslint from "@typescript-eslint/eslint-plugin";
import prettier from "eslint-plugin-prettier";
import tsParser from "@typescript-eslint/parser";
import path from "node:path";
import { fileURLToPath } from "node:url";
import js from "@eslint/js";
import { FlatCompat } from "@eslint/eslintrc";

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const compat = new FlatCompat({
    baseDirectory: __dirname,
    recommendedConfig: js.configs.recommended,
    allConfig: js.configs.all
});

export default [{
    ignores: ["**/out", "**/dist", "**/*.d.ts"],
}, ...compat.extends("prettier"), {
    plugins: {
        "@typescript-eslint": typescriptEslint,
        prettier,
    },

    languageOptions: {
        parser: tsParser,
        ecmaVersion: 6,
        sourceType: "module",
    },

    files: ["**/*.ts"],

    rules: {
        "@typescript-eslint/naming-convention": ["warn", {
            selector: "default",
            format: ["camelCase", "PascalCase"],
        }, {
            selector: "variable",
            format: ["camelCase", "UPPER_CASE"],
            leadingUnderscore: "allow",
        }, {
            selector: "property",
            format: ["camelCase", "UPPER_CASE"],
            leadingUnderscore: "allow",
        }, {
            selector: "parameter",
            format: ["camelCase"],
            leadingUnderscore: "allow",
        }, {
            selector: "typeLike",
            format: ["PascalCase"],
        }, {
            selector: "enumMember",
            format: ["UPPER_CASE"],
        }],

        "@/semi": "warn",
        curly: "warn",
        eqeqeq: "warn",
        "no-throw-literal": "warn",
        semi: "off",
        "prettier/prettier": "warn",
    },
}];