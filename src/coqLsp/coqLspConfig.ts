/* eslint-disable @typescript-eslint/naming-convention */
export interface CoqLspServerConfig {
    client_version: string;
    eager_diagnostics: boolean;
    goal_after_tactic: boolean;
    show_coq_info_messages: boolean;
    show_notices_as_diagnostics: boolean;
    admit_on_bad_qed: boolean;
    debug: boolean;
    unicode_completion: "off" | "normal" | "extended";
    max_errors: number;
    pp_type: 0 | 1 | 2;
    show_stats_on_hover: boolean;
}

export interface CoqLspClientConfig {
    coq_lsp_server_path: string;
    workspace_root_path?: string;
}

export namespace CoqLspConfig {
    export function createServerConfig(): CoqLspServerConfig {
        return {
            client_version: "0.2.2",
            eager_diagnostics: true,
            goal_after_tactic: false,
            show_coq_info_messages: false,
            show_notices_as_diagnostics: false,
            admit_on_bad_qed: true,
            debug: true,
            unicode_completion: "normal",
            max_errors: 1500000,
            pp_type: 1,
            show_stats_on_hover: false,
        };
    }

    export function createClientConfig(
        coqLspServerPath: string = "coq-lsp",
        workspaceRootPath?: string
    ): CoqLspClientConfig {
        let obj: CoqLspClientConfig = {
            coq_lsp_server_path: coqLspServerPath,
            workspace_root_path: workspaceRootPath,
        };
        return obj;
    }
}
