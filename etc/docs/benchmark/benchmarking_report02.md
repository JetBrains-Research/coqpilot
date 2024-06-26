# Experiments Report

We have conducted several experiments using the [imm project](https://github.com/weakmemory/imm). In this report we tell about the process of data preparations, used methods, conducted experiments, and their detailed results.

## Data Preparation

 We measured the performance of our solution on three groups of theorems. Grouping was done on the basis of length of human-written proofs measured in proof steps. Also the groups sizes were chosen with respect to the distribution of proofs lengths in the imm project. We have considered the theorems with proofs length in the interval $[3; 20]$. Such theorems amount to 84% of proofs from the imm project. We have randomly chosen theorems for each group. As the result we got 300 thereoms divided into the following groups:

| Group | Length Interval | Size |
|----------|----------|----------|
| A | 3 – 4   | 131 |
| B | 5 – 8   | 98 |
| C | 9 – 20  | 71 |

The list of the chosen theorems divided by groups you can find in the table provided in the [Results](#results) section.

In our experiments we compared different methods which can be used by CoqPilot:  Predefined tactic (`firstorder auto with *.`), OpenAI GPT-4o, OpenAI GPT-3.5, LLaMA-2 13B Chat, Anthropic Claude. Also, we used Tactician's tactic `synth`, and CoqHammer's `hammer` with timeouts of 30, 60, and 90 seconds for groups A, B, and C, respectively. If the proof was not found during the specified timeout, we consider the theorem as unsolved. We have used following parameters for each of the models:

### OpenAI GPT-4o 

```
{
    modelName: "openai-gpt-4o",
    choices: 12,

    systemPrompt: "..." ,


    newMessageMaxTokens: 2000,
    tokensLimit: 4096,

    multiroundProfile: ...,
    apiKey: "...",
}
```

### OpenAI GPT-3.5

```
{
    modelName: "openai-chat-gpt",
    choices: 20,

    systemPrompt: "..." ,


    newMessageMaxTokens: 800,
    tokensLimit: 2500,

    multiroundProfile: ...,
    apiKey: "...",
}
```

### LLaMA-2 13B Chat

```
{
    modelName: "grazie-chat-llama-v2-13b",
    choices: 20,

    systemPrompt: "..." ,


    newMessageMaxTokens: 160,
    tokensLimit: 1160,

    multiroundProfile: ...,
    apiKey: "...",
}

```

### Anthropic Claude

```
{
    modelName: "anthropic-claude",
    choices: 9,

    systemPrompt: "..." ,


    newMessageMaxTokens: 2000,
    tokensLimit: 4096,

    multiroundProfile: ...,
    apiKey: "...",
}
```


The `systemPrompt` used for all the models:

 

```
Generate proof of the theorem from user input in Coq. You should only generate proofs in Coq. Never add special comments to the proof. Your answer should be a valid Coq proof. It should start with 'Proof.' and end with 'Qed.'.
```

The `proofFixPrompt` used for all the models:

```
Unfortunately, the last proof is not correct. Here is the compiler's feedback: '${diagnostic}'. Please, fix the proof.
```

The `multiroundProfile` used for all the models:

```
{
    maxRoundsNumber: 1,
    proofFixChoices: 1,
    proofFixPrompt: "...",
}
```

The temperature parameter in all models was set to `1`.

## Results

In the table below you can find the results of our experiments. For each of the theorems we show its group and the methods which proved the theorem during our experiments.

| Group | File | Theorem Name | Predefined tactic | Anthropic Claude | OpenAI GPT-4o | OpenAI GPT-3.5 | Tactician | CoqHammer | LLaMA-2 13B Chat |
|-------|------|--------------|------------------|------------------|------------------|------------------|------------------|------------------|------------------|
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `issuableE` | [&#x2713;](#issuablee) | [&#x2713;](#issuablee) | [&#x2713;](#issuablee) | [&#x2713;](#issuablee) | [&#x2713;](#issuablee) | [&#x2713;](#issuablee) | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `issuedE` | [&#x2713;](#issuede) | &#x2717; | [&#x2713;](#issuede) | &#x2717; | [&#x2713;](#issuede) | [&#x2713;](#issuede) | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `deps_in_sb` | [&#x2713;](#deps_in_sb) | [&#x2713;](#deps_in_sb) | [&#x2713;](#deps_in_sb) | &#x2717; | &#x2717; | [&#x2713;](#deps_in_sb) | &#x2717; |
| A | [immToARMhelper.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToARMhelper.v) | `WF` | [&#x2713;](#wf) | &#x2717; | [&#x2713;](#wf) | &#x2717; | &#x2717; | [&#x2713;](#wf) | &#x2717; |
| A | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `iord_alt` | [&#x2713;](#iord_alt) | &#x2717; | [&#x2713;](#iord_alt) | &#x2717; | [&#x2713;](#iord_alt) | [&#x2713;](#iord_alt) | &#x2717; |
| A | [TSO.v](https://github.com/weakmemory/imm/tree/master/src/hardware/TSO.v) | `CON_WF` | [&#x2713;](#con_wf) | &#x2717; | [&#x2713;](#con_wf) | &#x2717; | &#x2717; | [&#x2713;](#con_wf) | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `reserved_union` | [&#x2713;](#reserved_union) | [&#x2713;](#reserved_union) | &#x2717; | [&#x2713;](#reserved_union) | [&#x2713;](#reserved_union) | [&#x2713;](#reserved_union) | &#x2717; |
| A | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `fr_eq` | [&#x2713;](#fr_eq) | &#x2717; | [&#x2713;](#fr_eq) | [&#x2713;](#fr_eq) | [&#x2713;](#fr_eq) | [&#x2713;](#fr_eq) | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `restr_eq_rel_same_loc` | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | &#x2717; |
| A | [AuxEE.v](https://github.com/weakmemory/imm/tree/master/src/travorder/AuxEE.v) | `E_E_trans` | [&#x2713;](#e_e_trans) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#e_e_trans) | &#x2717; |
| A | [imm_s_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_ppo.v) | `ppo_in_ar_int` | [&#x2713;](#ppo_in_ar_int) | &#x2717; | [&#x2713;](#ppo_in_ar_int) | [&#x2713;](#ppo_in_ar_int) | [&#x2713;](#ppo_in_ar_int) | [&#x2713;](#ppo_in_ar_int) | &#x2717; |
| A | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `step_preserves_instrs` | [&#x2713;](#step_preserves_instrs) | &#x2717; | [&#x2713;](#step_preserves_instrs) | &#x2717; | [&#x2713;](#step_preserves_instrs) | [&#x2713;](#step_preserves_instrs) | &#x2717; |
| A | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `sb_from_f_in_fwbob` | [&#x2713;](#sb_from_f_in_fwbob) | [&#x2713;](#sb_from_f_in_fwbob) | [&#x2713;](#sb_from_f_in_fwbob) | [&#x2713;](#sb_from_f_in_fwbob) | &#x2717; | [&#x2713;](#sb_from_f_in_fwbob) | [&#x2713;](#sb_from_f_in_fwbob) |
| A | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `sb_from_f_in_bob` | [&#x2713;](#sb_from_f_in_bob) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#sb_from_f_in_bob) | &#x2717; |
| A | [LDRF_Fsc.v](https://github.com/weakmemory/imm/tree/master/src/ldrf/LDRF_Fsc.v) | `ac_irr` | [&#x2713;](#ac_irr) | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#ac_irr) | &#x2717; | &#x2717; |
| A | [imm_s_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb.v) | `sw_in_hb` | &#x2717; | &#x2717; | [&#x2713;](#sw_in_hb) | [&#x2713;](#sw_in_hb) | [&#x2713;](#sw_in_hb) | [&#x2713;](#sw_in_hb) | [&#x2713;](#sw_in_hb) |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `Li_in_L` | &#x2717; | [&#x2713;](#li_in_l) | [&#x2713;](#li_in_l) | &#x2717; | [&#x2713;](#li_in_l) | [&#x2713;](#li_in_l) | &#x2717; |
| A | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `wf_urrD` | &#x2717; | [&#x2713;](#wf_urrd) | [&#x2713;](#wf_urrd) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `t_cur_in_t_acq` | &#x2717; | [&#x2713;](#t_cur_in_t_acq) | [&#x2713;](#t_cur_in_t_acq) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `re_dom` | &#x2717; | [&#x2713;](#re_dom) | [&#x2713;](#re_dom) | [&#x2713;](#re_dom) | [&#x2713;](#re_dom) | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_rfeE` | &#x2717; | [&#x2713;](#wf_rfee) | &#x2717; | [&#x2713;](#wf_rfee) | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `rfi_in_sb` | &#x2717; | [&#x2713;](#rfi_in_sb) | [&#x2713;](#rfi_in_sb) | [&#x2713;](#rfi_in_sb) | &#x2717; | [&#x2713;](#rfi_in_sb) | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `rmw_W_ex` | &#x2717; | [&#x2713;](#rmw_w_ex) | &#x2717; | [&#x2713;](#rmw_w_ex) | &#x2717; | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `covered_eq_ta_propagate` | &#x2717; | [&#x2713;](#covered_eq_ta_propagate) | [&#x2713;](#covered_eq_ta_propagate) | [&#x2713;](#covered_eq_ta_propagate) | [&#x2713;](#covered_eq_ta_propagate) | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_minus` | &#x2717; | [&#x2713;](#issued_minus) | [&#x2713;](#issued_minus) | &#x2717; | [&#x2713;](#issued_minus) | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `reserved_minus` | &#x2717; | [&#x2713;](#reserved_minus) | [&#x2713;](#reserved_minus) | &#x2717; | [&#x2713;](#reserved_minus) | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_singleton` | &#x2717; | [&#x2713;](#issued_singleton) | [&#x2713;](#issued_singleton) | [&#x2713;](#issued_singleton) | [&#x2713;](#issued_singleton) | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `set_minus_empty` | &#x2717; | [&#x2713;](#set_minus_empty) | &#x2717; | [&#x2713;](#set_minus_empty) | [&#x2713;](#set_minus_empty) | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rfrmw_issuable_in_I` | &#x2717; | [&#x2713;](#ar_rfrmw_issuable_in_i) | [&#x2713;](#ar_rfrmw_issuable_in_i) | &#x2717; | [&#x2713;](#ar_rfrmw_issuable_in_i) | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `rfrmw_rt_I_in_I` | &#x2717; | [&#x2713;](#rfrmw_rt_i_in_i) | [&#x2713;](#rfrmw_rt_i_in_i) | &#x2717; | [&#x2713;](#rfrmw_rt_i_in_i) | &#x2717; | &#x2717; |
| A | [imm_s_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb.v) | `hb_irr` | &#x2717; | [&#x2713;](#hb_irr) | &#x2717; | &#x2717; | [&#x2713;](#hb_irr) | &#x2717; | &#x2717; |
| A | [RMWinstrProps.v](https://github.com/weakmemory/imm/tree/master/src/basic/RMWinstrProps.v) | `rmw_is_rex_instr_rexmod` | &#x2717; | [&#x2713;](#rmw_is_rex_instr_rexmod) | [&#x2713;](#rmw_is_rex_instr_rexmod) | [&#x2713;](#rmw_is_rex_instr_rexmod) | &#x2717; | &#x2717; | &#x2717; |
| A | [RMWinstrProps.v](https://github.com/weakmemory/imm/tree/master/src/basic/RMWinstrProps.v) | `cas_produces_R_ex_instr_rexmod` | &#x2717; | [&#x2713;](#cas_produces_r_ex_instr_rexmod) | [&#x2713;](#cas_produces_r_ex_instr_rexmod) | [&#x2713;](#cas_produces_r_ex_instr_rexmod) | [&#x2713;](#cas_produces_r_ex_instr_rexmod) | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_dom_xmod` | &#x2717; | [&#x2713;](#same_lab_u2v_dom_xmod) | [&#x2713;](#same_lab_u2v_dom_xmod) | [&#x2713;](#same_lab_u2v_dom_xmod) | [&#x2713;](#same_lab_u2v_dom_xmod) | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `initninit_in_ext_sb` | &#x2717; | [&#x2713;](#initninit_in_ext_sb) | [&#x2713;](#initninit_in_ext_sb) | [&#x2713;](#initninit_in_ext_sb) | [&#x2713;](#initninit_in_ext_sb) | &#x2717; | &#x2717; |
| A | [AuxEE.v](https://github.com/weakmemory/imm/tree/master/src/travorder/AuxEE.v) | `rf_E_ENI` | &#x2717; | [&#x2713;](#rf_e_eni) | [&#x2713;](#rf_e_eni) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `fwbob_in_bob` | &#x2717; | [&#x2713;](#fwbob_in_bob) | [&#x2713;](#fwbob_in_bob) | [&#x2713;](#fwbob_in_bob) | &#x2717; | [&#x2713;](#fwbob_in_bob) | &#x2717; |
| A | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `fwbob_in_sb` | &#x2717; | [&#x2713;](#fwbob_in_sb) | [&#x2713;](#fwbob_in_sb) | [&#x2713;](#fwbob_in_sb) | [&#x2713;](#fwbob_in_sb) | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `rf_coverable` | &#x2717; | &#x2717; | [&#x2713;](#rf_coverable) | [&#x2713;](#rf_coverable) | [&#x2713;](#rf_coverable) | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `sc_coverable` | &#x2717; | &#x2717; | [&#x2713;](#sc_coverable) | [&#x2713;](#sc_coverable) | [&#x2713;](#sc_coverable) | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `ci_ii_in_ci` | &#x2717; | &#x2717; | [&#x2713;](#ci_ii_in_ci) | &#x2717; | [&#x2713;](#ci_ii_in_ci) | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `ii_in_sb` | &#x2717; | &#x2717; | [&#x2713;](#ii_in_sb) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `cc_in_sb` | &#x2717; | &#x2717; | [&#x2713;](#cc_in_sb) | &#x2717; | [&#x2713;](#cc_in_sb) | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `rfi_in_ii` | &#x2717; | &#x2717; | [&#x2713;](#rfi_in_ii) | &#x2717; | [&#x2713;](#rfi_in_ii) | [&#x2713;](#rfi_in_ii) | &#x2717; |
| A | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `furr_bunion` | &#x2717; | &#x2717; | [&#x2713;](#furr_bunion) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `co_co` | &#x2717; | &#x2717; | [&#x2713;](#co_co) | [&#x2713;](#co_co) | &#x2717; | [&#x2713;](#co_co) | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `ri_union_re` | &#x2717; | &#x2717; | [&#x2713;](#ri_union_re) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_coiD` | &#x2717; | &#x2717; | [&#x2713;](#wf_coid) | [&#x2713;](#wf_coid) | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_friD` | &#x2717; | &#x2717; | [&#x2713;](#wf_frid) | [&#x2713;](#wf_frid) | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_rfeD` | &#x2717; | &#x2717; | [&#x2713;](#wf_rfed) | [&#x2713;](#wf_rfed) | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `fri_in_sb` | &#x2717; | &#x2717; | [&#x2713;](#fri_in_sb) | [&#x2713;](#fri_in_sb) | &#x2717; | [&#x2713;](#fri_in_sb) | &#x2717; |
| A | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `FWBOB_irr` | &#x2717; | &#x2717; | [&#x2713;](#fwbob_irr) | [&#x2713;](#fwbob_irr) | [&#x2713;](#fwbob_irr) | [&#x2713;](#fwbob_irr) | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rfrmw_ct_I_in_I` | &#x2717; | &#x2717; | [&#x2713;](#ar_rfrmw_ct_i_in_i) | &#x2717; | [&#x2713;](#ar_rfrmw_ct_i_in_i) | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `W_ar_C_in_I` | &#x2717; | &#x2717; | [&#x2713;](#w_ar_c_in_i) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_W_sb_C_in_I` | &#x2717; | &#x2717; | [&#x2713;](#dom_w_sb_c_in_i) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `hb_trans` | &#x2717; | &#x2717; | [&#x2713;](#hb_trans) | [&#x2713;](#hb_trans) | &#x2717; | [&#x2713;](#hb_trans) | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_Rel` | &#x2717; | &#x2717; | [&#x2713;](#sub_rel) | &#x2717; | [&#x2713;](#sub_rel) | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_val` | &#x2717; | &#x2717; | [&#x2713;](#sub_val) | &#x2717; | [&#x2713;](#sub_val) | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_addr_in` | &#x2717; | &#x2717; | [&#x2713;](#sub_addr_in) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_rfi_in` | &#x2717; | &#x2717; | [&#x2713;](#sub_rfi_in) | &#x2717; | [&#x2713;](#sub_rfi_in) | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_rfe_in` | &#x2717; | &#x2717; | [&#x2713;](#sub_rfe_in) | &#x2717; | [&#x2713;](#sub_rfe_in) | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `tid_set_dec` | &#x2717; | &#x2717; | [&#x2713;](#tid_set_dec) | [&#x2713;](#tid_set_dec) | &#x2717; | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_dom_loc` | &#x2717; | &#x2717; | [&#x2713;](#same_lab_u2v_dom_loc) | [&#x2713;](#same_lab_u2v_dom_loc) | &#x2717; | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_dom_mod` | &#x2717; | &#x2717; | [&#x2713;](#same_lab_u2v_dom_mod) | [&#x2713;](#same_lab_u2v_dom_mod) | [&#x2713;](#same_lab_u2v_dom_mod) | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_is_rlx` | &#x2717; | &#x2717; | [&#x2713;](#same_lab_u2v_is_rlx) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_is_acqrel` | &#x2717; | &#x2717; | [&#x2713;](#same_lab_u2v_is_acqrel) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_label_u2v_trans` | &#x2717; | &#x2717; | [&#x2713;](#same_label_u2v_trans) | &#x2717; | [&#x2713;](#same_label_u2v_trans) | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `ext_sb_tid_init'` | &#x2717; | &#x2717; | [&#x2713;](#ext_sb_tid_init') | &#x2717; | [&#x2713;](#ext_sb_tid_init') | &#x2717; | &#x2717; |
| A | [imm_s_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_ppo.v) | `w_ex_acq_sb_w_in_ar_int` | &#x2717; | &#x2717; | [&#x2713;](#w_ex_acq_sb_w_in_ar_int) | [&#x2713;](#w_ex_acq_sb_w_in_ar_int) | [&#x2713;](#w_ex_acq_sb_w_in_ar_int) | [&#x2713;](#w_ex_acq_sb_w_in_ar_int) | &#x2717; |
| A | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `RMW_CTRL_FAIL'` | &#x2717; | &#x2717; | [&#x2713;](#rmw_ctrl_fail') | &#x2717; | [&#x2713;](#rmw_ctrl_fail') | [&#x2713;](#rmw_ctrl_fail') | &#x2717; |
| A | [imm_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_ppo.v) | `detour_in_ar_int` | &#x2717; | &#x2717; | [&#x2713;](#detour_in_ar_int) | &#x2717; | [&#x2713;](#detour_in_ar_int) | [&#x2713;](#detour_in_ar_int) | &#x2717; |
| A | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `bob_in_sb` | &#x2717; | &#x2717; | [&#x2713;](#bob_in_sb) | [&#x2713;](#bob_in_sb) | [&#x2713;](#bob_in_sb) | &#x2717; | &#x2717; |
| A | [CertCOhelper.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/CertCOhelper.v) | `col_in_co` | &#x2717; | &#x2717; | [&#x2713;](#col_in_co) | [&#x2713;](#col_in_co) | &#x2717; | &#x2717; | &#x2717; |
| A | [CertCOhelper.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/CertCOhelper.v) | `wf_colE` | &#x2717; | &#x2717; | [&#x2713;](#wf_cole) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `sw_covered` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#sw_covered) | [&#x2713;](#sw_covered) | &#x2717; | &#x2717; |
| A | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `iord_irreflexive` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#iord_irreflexive) | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `cr_hb_cr_hb` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#cr_hb_cr_hb) | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_rfe_acq_sb_issuable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#dom_rfe_acq_sb_issuable) | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `t_acq_covered` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#t_acq_covered) | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `ar_rf_ppo_loc_ct_issuable_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#ar_rf_ppo_loc_ct_issuable_in_i) | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_wex_sb_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#dom_wex_sb_issued) | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `rfi_rmw_in_sb_loc` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#rfi_rmw_in_sb_loc) | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `init_ninit_sb` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#init_ninit_sb) | &#x2717; | &#x2717; |
| A | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `IPROP_in_iord_simpl` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#iprop_in_iord_simpl) | [&#x2713;](#iprop_in_iord_simpl) | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_rfe_acq_sb_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#dom_rfe_acq_sb_issued) | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rfrmw_ct_CI_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#ar_rfrmw_ct_ci_in_i) | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `w_hb_loc_r_in_co_rf` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#w_hb_loc_r_in_co_rf) | &#x2717; | &#x2717; |
| A | [TLSCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TLSCoherency.v) | `init_exec_tls_disjoint` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#init_exec_tls_disjoint) | &#x2717; | &#x2717; |
| A | [Receptiveness.v](https://github.com/weakmemory/imm/tree/master/src/basic/Receptiveness.v) | `sim_execution_same_acts` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#sim_execution_same_acts) | [&#x2713;](#sim_execution_same_acts) | &#x2717; |
| A | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `bob_in_ar` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#bob_in_ar) | [&#x2713;](#bob_in_ar) | &#x2717; |
| A | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `rfrmw_in_im_co` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#rfrmw_in_im_co) | &#x2717; | &#x2717; |
| A | [OCamlToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/ocamlmm/OCamlToimm_s.v) | `sc_scb_pscb` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#sc_scb_pscb) | &#x2717; | &#x2717; |
| A | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `fr_co` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#fr_co) | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `ar_rf_ppo_loc_ct_I_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `W_Rel_sb_loc_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_detour_rmwrfi_rfe_acq_sb_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_F_Rel_sb_I_in_C-TC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_F_Rel_sb_I_in_C-ETO` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_detour_rfe_acq_sb_issued-TC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_detour_rfe_acq_sb_issued-ETO` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `urr_coverable-TC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `urr_coverable-ETO` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `ctrli_in_ctrl` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `ctrli_RW_in_ic` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `s_tm_union` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_sc_covered` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_c_rel_covered` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_s_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb.v) | `loceq_rs` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `w_hb_loc_w_in_co` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `release_in_hb_co` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `eco_sw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_sw_in` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `restrict_sub` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_imm_consistent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `same_loc_eq` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `complete_eq` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `F_AcqRel_eq` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_is_sc` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [AuxEE.v](https://github.com/weakmemory/imm/tree/master/src/travorder/AuxEE.v) | `sc_E_ENI` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `C_EXT_helper08` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `rf_sb_sc_rt_sb_fwbob_in_ar` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [JSMMToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/jsmm/JSMMToimm_s.v) | `hb_js_in_hb` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm_rfppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_rfppo.v) | `IMM_ar_rf_ppo_loc_ct_in_ar_ct` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [immToTSO.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToTSO.v) | `ct_psct` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfigAltOld.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfigAltOld.v) | `otc_rfirmw_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfigAlt.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfigAlt.v) | `tc_I_ar_rfrmw_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `ICOHs` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [Execution_eco.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution_eco.v) | `loceq_eco` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `t_acq_covered` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#t_acq_covered) | &#x2717; | &#x2717; |
| A | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_detour_rmwrfi_rfe_acq_sb_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `rmw_sb_W_in_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `ar_rf_ppo_loc_rt_I_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_dom_inclusion` | [&#x2713;](#same_lab_u2v_dom_inclusion) | &#x2717; | [&#x2713;](#same_lab_u2v_dom_inclusion) | [&#x2713;](#same_lab_u2v_dom_inclusion) | [&#x2713;](#same_lab_u2v_dom_inclusion) | &#x2717; | &#x2717; |
| B | [C11Toimm_s.v](https://github.com/weakmemory/imm/tree/master/src/c11/C11Toimm_s.v) | `s_imm_consistentimplies_c11_consistent` | [&#x2713;](#s_imm_consistentimplies_c11_consistent) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#s_imm_consistentimplies_c11_consistent) | &#x2717; |
| B | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_ar_ct_issuable` | &#x2717; | [&#x2713;](#dom_ar_ct_issuable) | &#x2717; | [&#x2713;](#dom_ar_ct_issuable) | [&#x2713;](#dom_ar_ct_issuable) | &#x2717; | &#x2717; |
| B | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_SB` | &#x2717; | [&#x2713;](#sub_sb) | [&#x2713;](#sub_sb) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `wf_ci0E` | &#x2717; | [&#x2713;](#wf_ci0e) | [&#x2713;](#wf_ci0e) | [&#x2713;](#wf_ci0e) | &#x2717; | &#x2717; | &#x2717; |
| B | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_eq_ta_issue` | &#x2717; | [&#x2713;](#issued_eq_ta_issue) | [&#x2713;](#issued_eq_ta_issue) | [&#x2713;](#issued_eq_ta_issue) | [&#x2713;](#issued_eq_ta_issue) | &#x2717; | &#x2717; |
| B | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `FWBOB_trans` | &#x2717; | [&#x2713;](#fwbob_trans) | &#x2717; | &#x2717; | [&#x2713;](#fwbob_trans) | &#x2717; | &#x2717; |
| B | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `depf_preserves_set_lexpr` | &#x2717; | [&#x2713;](#depf_preserves_set_lexpr) | [&#x2713;](#depf_preserves_set_lexpr) | [&#x2713;](#depf_preserves_set_lexpr) | [&#x2713;](#depf_preserves_set_lexpr) | &#x2717; | &#x2717; |
| B | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `wf_fwbobE` | &#x2717; | [&#x2713;](#wf_fwbobe) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power.v) | `wf_hbD` | &#x2717; | &#x2717; | [&#x2713;](#wf_hbd) | [&#x2713;](#wf_hbd) | &#x2717; | &#x2717; | &#x2717; |
| B | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `wf_S_tmrD` | &#x2717; | &#x2717; | [&#x2713;](#wf_s_tmrd) | [&#x2713;](#wf_s_tmrd) | &#x2717; | &#x2717; | &#x2717; |
| B | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `urr_alt` | &#x2717; | &#x2717; | [&#x2713;](#urr_alt) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `same_lab_u2v_dom_trans` | &#x2717; | &#x2717; | [&#x2713;](#same_lab_u2v_dom_trans) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `tid_n_init_ext_sb` | &#x2717; | &#x2717; | [&#x2713;](#tid_n_init_ext_sb) | &#x2717; | [&#x2713;](#tid_n_init_ext_sb) | &#x2717; | &#x2717; |
| B | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `sim_clos_empty` | &#x2717; | &#x2717; | [&#x2713;](#sim_clos_empty) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `sim_clos_dist` | &#x2717; | &#x2717; | [&#x2713;](#sim_clos_dist) | [&#x2713;](#sim_clos_dist) | [&#x2713;](#sim_clos_dist) | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_addrE` | &#x2717; | &#x2717; | [&#x2713;](#wf_addre) | [&#x2713;](#wf_addre) | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_depsD` | &#x2717; | &#x2717; | [&#x2713;](#wf_depsd) | [&#x2713;](#wf_depsd) | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `same_tid_trans` | &#x2717; | &#x2717; | [&#x2713;](#same_tid_trans) | [&#x2713;](#same_tid_trans) | [&#x2713;](#same_tid_trans) | [&#x2713;](#same_tid_trans) | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `wf_cc0D` | &#x2717; | &#x2717; | [&#x2713;](#wf_cc0d) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_is_ta_propagate_to_G` | &#x2717; | &#x2717; | [&#x2713;](#issued_is_ta_propagate_to_g) | [&#x2713;](#issued_is_ta_propagate_to_g) | [&#x2713;](#issued_is_ta_propagate_to_g) | &#x2717; | &#x2717; |
| B | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `covered_ta_reserve` | &#x2717; | &#x2717; | [&#x2713;](#covered_ta_reserve) | [&#x2713;](#covered_ta_reserve) | [&#x2713;](#covered_ta_reserve) | &#x2717; | &#x2717; |
| B | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `wf_ar_rfrmwE` | &#x2717; | &#x2717; | [&#x2713;](#wf_ar_rfrmwe) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `eSB_in_sb_sc_ct` | &#x2717; | &#x2717; | [&#x2713;](#esb_in_sb_sc_ct) | &#x2717; | [&#x2713;](#esb_in_sb_sc_ct) | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rf_ppo_loc_rt_I_in_I` | &#x2717; | &#x2717; | [&#x2713;](#ar_rf_ppo_loc_rt_i_in_i) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rt_I_in_I` | &#x2717; | &#x2717; | [&#x2713;](#ar_rt_i_in_i) | &#x2717; | [&#x2713;](#ar_rt_i_in_i) | &#x2717; | &#x2717; |
| B | [TraversalConfigAltOld.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfigAltOld.v) | `otc_dr_ppo_I` | &#x2717; | &#x2717; | [&#x2713;](#otc_dr_ppo_i) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Receptiveness.v](https://github.com/weakmemory/imm/tree/master/src/basic/Receptiveness.v) | `TWF_helper_rmw` | &#x2717; | &#x2717; | [&#x2713;](#twf_helper_rmw) | [&#x2713;](#twf_helper_rmw) | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_bob.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_bob.v) | `wf_bobE` | &#x2717; | &#x2717; | [&#x2713;](#wf_bobe) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_fences.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_fences.v) | `wf_fenceD` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#wf_fenced) | &#x2717; | &#x2717; | &#x2717; |
| B | [Arm.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Arm.v) | `deps_in_ctrl_or_dob` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#deps_in_ctrl_or_dob) | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_s_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_ppo.v) | `rmw_in_ppo` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#rmw_in_ppo) | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `ar_rt_CI_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#ar_rt_ci_in_i) | &#x2717; | &#x2717; |
| B | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `restrict_threads_bound` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#restrict_threads_bound) | &#x2717; | &#x2717; |
| B | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_IPROP` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#sub_iprop) | &#x2717; | &#x2717; |
| B | [Events.v](https://github.com/weakmemory/imm/tree/master/src/basic/Events.v) | `ext_sb_semi_total_r` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#ext_sb_semi_total_r) | &#x2717; | &#x2717; |
| B | [imm_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_ppo.v) | `rmw_sb_W_in_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#rmw_sb_w_in_ppo) | &#x2717; | &#x2717; |
| B | [Execution_eco.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution_eco.v) | `coi_coe` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#coi_coe) | &#x2717; | &#x2717; |
| B | [Arm.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Arm.v) | `dob_alt` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#dob_alt) | &#x2717; | &#x2717; |
| B | [TLSCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TLSCoherency.v) | `tls_coherent_ext` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#tls_coherent_ext) | &#x2717; | &#x2717; |
| B | [CertCOhelper.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/CertCOhelper.v) | `col_trans` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#col_trans) | &#x2717; | &#x2717; |
| B | [imm_s_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb.v) | `release_rf_rmw_steps` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#release_rf_rmw_steps) | &#x2717; | &#x2717; |
| B | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issuable_iord_dom_cond` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#issuable_iord_dom_cond) | &#x2717; |
| B | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `istep_eindex_shift` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#istep_eindex_shift) | &#x2717; |
| B | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `msg_rel_issued-TC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `msg_rel_issued-ETO` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power.v) | `fence_hb_fri` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power.v) | `S_rw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power.v) | `rw_S` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `urr_hb_sc_hb_irr` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `furr_hb_sc_hb_irr` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_ppo.v) | `fwbob_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `W_ex_eq_EW_W_ex` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `codom_rfi_rfe_empty` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `rf_rmw_sb_minus_sb` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `wf_rmw_invf` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `detour_transp_rfi` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_fences.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_fences.v) | `lwsync_alt` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_fences.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_fences.v) | `RW_sb_lwsync_in_lwsync` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `rdw_rbi_in_rbi` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `basic_to_transitional` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `addrsbW_in_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `wf_helperE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `L_in_union` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `wf_ppoD` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issuedW` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_rfppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_rfppo.v) | `IMM_no_ar_rf_ppo_loc_to_init` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `wf_ar_rfrmw_ctE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `wf_ar_rf_ppo_locE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `rfe_rmw_in_ar_ct` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_s.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s.v) | `wf_pscE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [AuxEE.v](https://github.com/weakmemory/imm/tree/master/src/travorder/AuxEE.v) | `furr_E_ENI_cr` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `dom_rel_tls_helper` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TlsAux2.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsAux2.v) | `tls_coherent_more` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Execution_eco.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution_eco.v) | `eco_refl` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_detour_rfe_ppo_issuable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `rf_ppo_loc_rt_I_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_c_rel_coverable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_sw_coverable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [IordCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/IordCoherency.v) | `init_tls_iord_coherent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `wf_releaseE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `wf_swD` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `F_sw_eq` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `rmw_sw_eq` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm.v) | `wf_arE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `same_lab_u2v_dom_restricted` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `step_empty_same_E` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalConfigAltOld.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfigAltOld.v) | `otc_W_bob_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TraversalConfigAltOld.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfigAltOld.v) | `otc_tc_fwbob_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [CertCOhelper.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/CertCOhelper.v) | `T_I_new_co_I_T` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_sToARM.v](https://github.com/weakmemory/imm/tree/master/src/hardware/imm_sToARM.v) | `C_SC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm_sToARM.v](https://github.com/weakmemory/imm/tree/master/src/hardware/imm_sToARM.v) | `RMW_COI` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [FinExecution.v](https://github.com/weakmemory/imm/tree/master/src/basic/FinExecution.v) | `fin_exec_full_equiv` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [SimIordTraversal.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimIordTraversal.v) | `trav_prefix_union_init_tls_coherent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [ViewRelHelpers.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/ViewRelHelpers.v) | `t_rel_fence_step` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [TlsViewRelHelpers.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsViewRelHelpers.v) | `t_rel_msg_rel_rfrmw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [OCamlToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/ocamlmm/OCamlToimm_s.v) | `sb_rf_sc_sc` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [LDRF_Fsc.v](https://github.com/weakmemory/imm/tree/master/src/ldrf/LDRF_Fsc.v) | `sb_f_at` | [&#x2713;](#sb_f_at) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `wf_ii0E` | &#x2717; | [&#x2713;](#wf_ii0e) | [&#x2713;](#wf_ii0e) | [&#x2713;](#wf_ii0e) | &#x2717; | &#x2717; | &#x2717; |
| C | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `step_threads_set` | &#x2717; | [&#x2713;](#step_threads_set) | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Receptiveness.v](https://github.com/weakmemory/imm/tree/master/src/basic/Receptiveness.v) | `is_r_increasing` | &#x2717; | [&#x2713;](#is_r_increasing) | [&#x2713;](#is_r_increasing) | [&#x2713;](#is_r_increasing) | &#x2717; | &#x2717; | &#x2717; |
| C | [TLSCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TLSCoherency.v) | `tlsc_I_in_W` | &#x2717; | [&#x2713;](#tlsc_i_in_w) | [&#x2713;](#tlsc_i_in_w) | [&#x2713;](#tlsc_i_in_w) | &#x2717; | &#x2717; | &#x2717; |
| C | [Rel_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Rel_opt.v) | `F_Rel_eq` | &#x2717; | [&#x2713;](#f_rel_eq) | [&#x2713;](#f_rel_eq) | &#x2717; | [&#x2713;](#f_rel_eq) | &#x2717; | &#x2717; |
| C | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `t_rel_other_thread` | &#x2717; | &#x2717; | [&#x2713;](#t_rel_other_thread) | &#x2717; | [&#x2713;](#t_rel_other_thread) | &#x2717; | &#x2717; |
| C | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_C_in_CI` | &#x2717; | &#x2717; | [&#x2713;](#ar_c_in_ci) | &#x2717; | [&#x2713;](#ar_c_in_ci) | &#x2717; | &#x2717; |
| C | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `dom_rel_collect_event` | &#x2717; | &#x2717; | [&#x2713;](#dom_rel_collect_event) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_ta_issue` | &#x2717; | &#x2717; | [&#x2713;](#issued_ta_issue) | &#x2717; | [&#x2713;](#issued_ta_issue) | &#x2717; | &#x2717; |
| C | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `issued_EW` | &#x2717; | &#x2717; | [&#x2713;](#issued_ew) | &#x2717; | [&#x2713;](#issued_ew) | &#x2717; | &#x2717; |
| C | [TLSCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TLSCoherency.v) | `iord_exec_tls_cip` | &#x2717; | &#x2717; | [&#x2713;](#iord_exec_tls_cip) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimTraversalProperties.v](https://github.com/weakmemory/imm/tree/master/src/traversal/SimTraversalProperties.v) | `isim_trav_step_new_issued_tid` | &#x2717; | &#x2717; | [&#x2713;](#isim_trav_step_new_issued_tid) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `reserved_ta_reserve` | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#reserved_ta_reserve) | &#x2717; | &#x2717; | &#x2717; |
| C | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `rel_clos_idemp` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#rel_clos_idemp) | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_sb_W_rel_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#dom_sb_w_rel_issued) | &#x2717; | &#x2717; |
| C | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `sb_semi_total_r` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `co_E_W_Loc` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Execution.v](https://github.com/weakmemory/imm/tree/master/src/basic/Execution.v) | `rmw_rf_rt_1` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_s_rfppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_rfppo.v) | `no_ar_rfppo_rt_to_init` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `rel_clos_exec_tls` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `sim_clos_sim_coherent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `rmw_clos_once` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimClosure.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimClosure.v) | `iiord_step_minus_reserved` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [FinThreads.v](https://github.com/weakmemory/imm/tree/master/src/basic/FinThreads.v) | `BinPos_lt_fin` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_sToARM.v](https://github.com/weakmemory/imm/tree/master/src/hardware/imm_sToARM.v) | `IMM_s_psc_consistent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [LDRF_Fsc.v](https://github.com/weakmemory/imm/tree/master/src/ldrf/LDRF_Fsc.v) | `imm_to_ocaml_causal` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SubExecution.v](https://github.com/weakmemory/imm/tree/master/src/imm/SubExecution.v) | `sub_iord` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [CombRelations.v](https://github.com/weakmemory/imm/tree/master/src/imm/CombRelations.v) | `urr_f_sc` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `dom_sb_sc_ct_coverable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `hb_coverable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToARMhelper.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToARMhelper.v) | `W_ex_acq_sb_in_boba1` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToARMhelper.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToARMhelper.v) | `hb_f_sy_in_ord` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `Li_is_ii` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Power_ppo.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_ppo.v) | `ct_ppo_ctrli_rw_in_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `wf_rsE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `wf_swE` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_hb.v) | `rs_rf_rmw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `IPROP_fsupp` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TraversalOrder.v) | `AR_fsupp` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Traversal.v](https://github.com/weakmemory/imm/tree/master/src/traversal/Traversal.v) | `trav_step_coherence` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Traversal.v](https://github.com/weakmemory/imm/tree/master/src/traversal/Traversal.v) | `itrav_step_mon_ext_cover` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `steps_preserve_lab` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [ProgToExecutionProperties.v](https://github.com/weakmemory/imm/tree/master/src/basic/ProgToExecutionProperties.v) | `tid_initi` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TlsViewRelHelpers.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsViewRelHelpers.v) | `t_cur_msg_rel_rfrmw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `sw_in_sw_big` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `rs_in_rs_big` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToPower.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToPower.v) | `W_ex_rfi_R_Acq_ct_step` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_s_ppo.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_ppo.v) | `ppo_rfi_ppo` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TlsEventSets.v](https://github.com/weakmemory/imm/tree/master/src/travorder/TlsEventSets.v) | `init_propagated_thread` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `ar_rf_ppo_loc_rt_CI_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `W_rel_sb_loc_W_CI` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `init_issued` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `dom_detour_rfe_acq_sb_issuable` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [TraversalConfig.v](https://github.com/weakmemory/imm/tree/master/src/traversal/TraversalConfig.v) | `rf_ppo_loc_coverable_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [IordCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/IordCoherency.v) | `iord_coherent_equiv_wo_reserved` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [IordCoherency.v](https://github.com/weakmemory/imm/tree/master/src/travorder/IordCoherency.v) | `iord_coherent_crt` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [ReserveClos.v](https://github.com/weakmemory/imm/tree/master/src/travorder/ReserveClos.v) | `reserve_clos_init_tls` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [immToTSO.v](https://github.com/weakmemory/imm/tree/master/src/hardware/immToTSO.v) | `psc_ft` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Sc_opt.v](https://github.com/weakmemory/imm/tree/master/src/imm/Sc_opt.v) | `psc_base_rw_rw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [OCamlToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/ocamlmm/OCamlToimm_s.v) | `sbnl_hb_scb` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [OCamlToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/ocamlmm/OCamlToimm_s.v) | `imm_to_ocaml_consistent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_s_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb.v) | `hb_first_Rel` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [Power_fences.v](https://github.com/weakmemory/imm/tree/master/src/hardware/Power_fences.v) | `fence_trans` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [CertCOhelper.v](https://github.com/weakmemory/imm/tree/master/src/simhelpers/CertCOhelper.v) | `co_for_split` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_sToimm.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_sToimm.v) | `imm_consistentimplies_s_imm_psc_consistent` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [JSMMToimm_s.v](https://github.com/weakmemory/imm/tree/master/src/jsmm/JSMMToimm_s.v) | `sw_js_in_sw` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm_s_hb_hb.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm_s_hb_hb.v) | `s_rs_in_rs` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm.v](https://github.com/weakmemory/imm/tree/master/src/imm/imm.v) | `CoherentPSC` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [SimIordTraversal.v](https://github.com/weakmemory/imm/tree/master/src/travorder/SimIordTraversal.v) | `sim_traversal_inf_full` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [EventsTraversalOrder.v](https://github.com/weakmemory/imm/tree/master/src/travorder/EventsTraversalOrder.v) | `ar_rf_ppo_loc_ct_issuable_in_I` | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |

## Generated Proofs

Here you can find the generated proofs for each of the proved theorems during the experiments.

### Group A

#### Theorem name: 
#### `issuableE`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Anthropic Claude Proof:

```
 {  
unfold issuable; basic_solver.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold issuable; basic_solver.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold issuable; basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `issuedE`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { rewrite issued_in_issuable.
by apply issuableE. }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `deps_in_sb`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Anthropic Claude Proof:

```
 {  
unfold deps.
rewrite (data_in_sb WF).
rewrite (ctrl_in_sb WF).
rewrite (addr_in_sb WF).
Set Printing All.
basic_solver.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold deps.
rewrite (data_in_sb WF).
rewrite (addr_in_sb WF).
rewrite (ctrl_in_sb WF).
basic_solver.

 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `WF`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { apply CON. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `iord_alt`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold iord. 
unfold iord_simpl.
basic_solver. 

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `CON_WF`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { split; try apply CON; auto. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `reserved_union`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Anthropic Claude Proof:

```
 { 
unfold reserved.
basic_solver 10.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold reserved.
split; basic_solver 10.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `fr_eq`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { 
by unfold Execution.fr; rewrite rf_eq, co_eq.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; unfolder; ins; desf; eauto.
all: rewrite <- F_Rel_eq, <- FR_Rel_eq, <- R_Acq_eq, <- FR_Acq_eq, <- W_ex_acq_eq in *;
     rewrite <- same_loc_eq, <- F_Sc_eq, <- Acq_or_W_eq in *.
all: try solve [type_solver].
all: try solve [exfalso; type_solver].
all: try solve [exfalso; eauto using (rmw_in_sb_loc G)].
all: try solve [exfalso; eauto using (rmw_in_sb_dom G)].
all: try solve [exfalso; eauto using (rf_rmw_in_sb G)].
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `restr_eq_rel_same_loc`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Anthropic Claude Proof:

```
 { 
unfold same_loc. 
unfolder.
split; ins; desf; auto.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold same_loc; basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold same_loc; basic_solver.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `E_E_trans`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `ppo_in_ar_int`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { unfold ar_int.
basic_solver 10. }
```

#### OpenAI GPT-3.5 Proof:

```
 { unfold ar_int.
  unfold ppo.
  basic_solver 20. }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `step_preserves_instrs`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { destruct STEP as [ll STEP].
cdes STEP.
by destruct ISTEP0. }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `sb_from_f_in_fwbob`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### LLaMA-2 13B Chat Proof:

```
 { 
unfold fwbob.
basic_solver 10.
 }
```

#### Anthropic Claude Proof:

```
 { 
unfold fwbob.
basic_solver 10.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold fwbob.
basic_solver 10. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold fwbob.
basic_solver 10.
 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `sb_from_f_in_bob`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `ac_irr`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sw_in_hb`

#### LLaMA-2 13B Chat Proof:

```
 { 
vauto.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold hb.
rewrite <- ct_step; basic_solver 10.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold sw, hb; relsf; unionL; eauto with hahn.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `Li_in_L`

#### Anthropic Claude Proof:

```
 {  
rewrite Li_is_ii, L_is_ic.
by apply ii_in_ic.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfolder; ins; vauto. }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `wf_urrD`

#### Anthropic Claude Proof:

```
 { 
split; [|basic_solver]. 
unfold urr.
basic_solver 21.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
split.
- unfold urr.
  basic_solver 21.
- basic_solver.

 }
```

#### Theorem name: 
#### `t_cur_in_t_acq`

#### Anthropic Claude Proof:

```
 {  
unfold t_cur, t_acq, c_cur, c_acq.
basic_solver 21.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold t_cur, t_acq, c_cur, c_acq.
basic_solver 21. }
```

#### Theorem name: 
#### `re_dom`

#### Anthropic Claude Proof:

```
 {  
rewrite DOM at 1; basic_solver.

 }
```

#### OpenAI GPT-4o Proof:

```
 { 
rewrite DOM at 1; basic_solver.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite DOM.
rewrite <- seqA.
assert (r \ sb ⊆ r) as Hr.
by unfolder; ins; desf; eauto.
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `wf_rfeE`

#### Anthropic Claude Proof:

```
 {   
split; [|basic_solver].
apply (re_dom (wf_rfE WF)).
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold rfe.
rewrite (wf_rfE WF) at 1.
basic_solver.
 }
```

#### Theorem name: 
#### `rfi_in_sb`

#### Anthropic Claude Proof:

```
 {  
unfold rfi.
rewrite rfi_union_rfe.
basic_solver.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold rfi.
basic_solver.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold rfi, sb; basic_solver.
 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `rmw_W_ex`

#### Anthropic Claude Proof:

```
 {  
unfold rmw, W_ex.
basic_solver.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold rmw, W_ex.
basic_solver.
 }
```

#### Theorem name: 
#### `covered_eq_ta_propagate`

#### Anthropic Claude Proof:

```
 {  
unfold covered.
split; try basic_solver 10.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold covered.
clear.
basic_solver 10. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold covered.
clear.
basic_solver 10.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `issued_minus`

#### Anthropic Claude Proof:

```
 {  
apply tls_set_minus_helper.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
apply tls_set_minus_helper.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `reserved_minus`

#### Anthropic Claude Proof:

```
 { 
unfold reserved.
apply tls_set_minus_helper.

 }
```

#### OpenAI GPT-4o Proof:

```
 { 
apply tls_set_minus_helper.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `issued_singleton`

#### Anthropic Claude Proof:

```
 { 
unfold issued.
basic_solver.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold issued.
split; basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold issued.
unfold mkTL.
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `set_minus_empty`

#### Anthropic Claude Proof:

```
 { 
unfolder.
split; ins; desf.
eauto.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold set_minus.
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ar_rfrmw_issuable_in_I`

#### Anthropic Claude Proof:

```
 { 
rewrite (rmw_in_ppo_loc WF).
apply ar_rf_ppo_loc_issuable_in_I.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
rewrite (rmw_in_ppo_loc WF).
apply ar_rf_ppo_loc_issuable_in_I.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rfrmw_rt_I_in_I`

#### Anthropic Claude Proof:

```
 { 
apply dom_rel_clos_refl_trans_eqv.
rewrite seqA.
by apply rfrmw_I_in_I.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
apply dom_rel_clos_refl_trans_eqv.
rewrite seqA.
apply rfrmw_I_in_I.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `hb_irr`

#### Anthropic Claude Proof:

```
 { 
red in COH; unfolder in COH; basic_solver 12.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rmw_is_rex_instr_rexmod`

#### Anthropic Claude Proof:

```
 { 
symmetry in ISTEP; apply nth_error_In in ISTEP. 
apply RMWREX in ISTEP; simpls; desf.
 }
```

#### OpenAI GPT-4o Proof:

```
 { symmetry in ISTEP; apply nth_error_In in ISTEP.
apply RMWREX in ISTEP; simpls; desf. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
symmetry in ISTEP.
apply nth_error_In in ISTEP.
apply RMWREX in ISTEP; simpls; desf.
 }
```

#### Theorem name: 
#### `cas_produces_R_ex_instr_rexmod`

#### Anthropic Claude Proof:

```
 { symmetry in ISTEP.
apply nth_error_In in ISTEP.
apply RMWREX in ISTEP. 
simpl in ISTEP.
desf. }
```

#### OpenAI GPT-4o Proof:

```
 { 
symmetry in ISTEP; apply nth_error_In in ISTEP.
apply RMWREX in ISTEP; simpls; desf.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
symmetry in ISTEP.
apply nth_error_In in ISTEP.
apply RMWREX in ISTEP.
simpls; desf.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `same_lab_u2v_dom_xmod`

#### Anthropic Claude Proof:

```
 { 
same_lab_set_solver_f SAME.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
same_lab_set_solver_f SAME.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
same_lab_set_solver_f SAME.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `initninit_in_ext_sb`

#### Anthropic Claude Proof:

```
 { 
unfold ext_sb.
basic_solver 10.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold is_init, ext_sb; basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold ext_sb; basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rf_E_ENI`

#### Anthropic Claude Proof:

```
 { 
rewrite wf_rfE, no_rf_to_init; auto.
basic_solver.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
rewrite wf_rfE, no_rf_to_init; auto.
basic_solver.
 }
```

#### Theorem name: 
#### `fwbob_in_bob`

#### Anthropic Claude Proof:

```
 { 
unfold fwbob, bob.
by relsf.
 }
```

#### OpenAI GPT-4o Proof:

```
 { unfold bob; basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { unfold bob, fwbob.
basic_solver 12. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `fwbob_in_sb`

#### Anthropic Claude Proof:

```
 {  
unfold fwbob, bob.
basic_solver 12.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold fwbob.
basic_solver.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { unfold fwbob.
basic_solver. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rf_coverable`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite (dom_rel_helper dom_rf_coverable).
basic_solver.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite (dom_rel_helper dom_rf_coverable).
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sc_coverable`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite (dom_rel_helper dom_sc_coverable); auto.
basic_solver.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite (dom_rel_helper dom_sc_coverable).
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ci_ii_in_ci`

#### OpenAI GPT-4o Proof:

```
 { unfolder; ins; desf; vauto. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ii_in_sb`

#### OpenAI GPT-4o Proof:

```
 { 
unfolder; ins; splits; try done; eapply in_sb_helper in H; desf.
 }
```

#### Theorem name: 
#### `cc_in_sb`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite cc_in_ic.
apply ic_in_sb; auto.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rfi_in_ii`

#### OpenAI GPT-4o Proof:

```
 { unfolder; intros x y H.
red in H; desf.
vauto. }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `furr_bunion`

#### OpenAI GPT-4o Proof:

```
 { unfold furr; basic_solver 21. }
```

#### Theorem name: 
#### `co_co`

#### OpenAI GPT-4o Proof:

```
 { by generalize co_trans; basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite wf_coE; auto.
generalize co_trans.
basic_solver.
 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `ri_union_re`

#### OpenAI GPT-4o Proof:

```
 { split.
- unfolder; ins; tauto.
- unfolder; ins; tauto. }
```

#### Theorem name: 
#### `wf_coiD`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
apply (ri_dom (wf_coD WF)).

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold coi.
rewrite (wf_coE WF) at 1.
rewrite (wf_coD WF) at 1.
rewrite (wf_coE WF) at 2.
rewrite (wf_coD WF) at 2.
basic_solver.
 }
```

#### Theorem name: 
#### `wf_friD`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
apply (ri_dom (wf_frD WF)).

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold fri; rewrite (wf_frD WF) at 1; basic_solver.
 }
```

#### Theorem name: 
#### `wf_rfeD`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
apply (re_dom (wf_rfD WF)).

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold rfe; rewrite (wf_rfD WF) at 1; basic_solver.
 }
```

#### Theorem name: 
#### `fri_in_sb`

#### OpenAI GPT-4o Proof:

```
 { 
unfold fri.
unfold Execution.sb.
basic_solver.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold fri, sb; basic_solver.
 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `FWBOB_irr`

#### OpenAI GPT-4o Proof:

```
 { iord_dom_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold FWBOB.
unfolder; ins; desc.
unfold seq in *; desc.
congruence.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `ar_rfrmw_ct_I_in_I`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite (rmw_in_ppo_loc WF).
apply ar_rf_ppo_loc_ct_I_in_I.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `W_ar_C_in_I`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite covered_in_coverable at 1; eauto.
apply W_ar_coverable_in_I.
 }
```

#### Theorem name: 
#### `dom_W_sb_C_in_I`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite sb_covered; auto.
etransitivity.
2: by eapply w_covered_issued; eauto.
basic_solver.

 }
```

#### Theorem name: 
#### `hb_trans`

#### OpenAI GPT-4o Proof:

```
 { unfold hb; apply transitive_ct. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold hb.
apply transitive_ct.
 }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `sub_Rel`

#### OpenAI GPT-4o Proof:

```
 { 
by rewrite (sub_lab SUB).

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sub_val`

#### OpenAI GPT-4o Proof:

```
 { 
unfold val.
rewrite (sub_lab SUB).
reflexivity.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sub_addr_in`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite sub_addr; basic_solver.

 }
```

#### Theorem name: 
#### `sub_rfi_in`

#### OpenAI GPT-4o Proof:

```
 { 
unfold Execution.rfi.
by rewrite sub_sb_in, sub_rf_in.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sub_rfe_in`

#### OpenAI GPT-4o Proof:

```
 { 
unfold Execution.rfe.
rewrite (sub_rf SUB), sub_sb.
basic_solver 21.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `tid_set_dec`

#### OpenAI GPT-4o Proof:

```
 { unfolder.
split.
- firstorder.
- ins.
  destruct (classic (tid x = thread)); auto. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold set_union, set_equiv, set_subset; split; ins; desf; tauto.
 }
```

#### Theorem name: 
#### `same_lab_u2v_dom_loc`

#### OpenAI GPT-4o Proof:

```
 { same_lab_set_solver_f SAME. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
same_lab_set_solver_f SAME.
 }
```

#### Theorem name: 
#### `same_lab_u2v_dom_mod`

#### OpenAI GPT-4o Proof:

```
 { same_lab_set_solver_f SAME. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
same_lab_set_solver_f SAME.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `same_lab_u2v_is_rlx`

#### OpenAI GPT-4o Proof:

```
 { 
generalize (same_lab_u2v_dom_is_rlx SAME).
relsf.

 }
```

#### Theorem name: 
#### `same_lab_u2v_is_acqrel`

#### OpenAI GPT-4o Proof:

```
 { generalize (same_lab_u2v_dom_is_acqrel SAME).
relsf. }
```

#### Theorem name: 
#### `same_label_u2v_trans`

#### OpenAI GPT-4o Proof:

```
 { unfold same_label_u2v in *; desf; desf. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ext_sb_tid_init'`

#### OpenAI GPT-4o Proof:

```
 { 
unfolder.
ins.
destruct x, y; unfold is_init, same_tid, tid, ext_sb in *; desf; eauto.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `w_ex_acq_sb_w_in_ar_int`

#### OpenAI GPT-4o Proof:

```
 { unfold ar_int.
basic_solver 10. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold ar_int.
rewrite wf_sbE at 1.
basic_solver 12.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `RMW_CTRL_FAIL'`

#### OpenAI GPT-4o Proof:

```
 { 
intros.
rewrite RMW_CTRL_FAIL.
basic_solver.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `detour_in_ar_int`

#### OpenAI GPT-4o Proof:

```
 { 
unfold ar_int.
basic_solver.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `bob_in_sb`

#### OpenAI GPT-4o Proof:

```
 { 
unfold bob.
unfold fwbob.
basic_solver 12.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { unfold bob, fwbob.
basic_solver. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `col_in_co`

#### OpenAI GPT-4o Proof:

```
 { 
unfold col; unfolder; intros x y [Hloc Hco].
apply Hco.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold col.
rewrite wf_coD, wf_coE.
basic_solver.
 }
```

#### Theorem name: 
#### `wf_colE`

#### OpenAI GPT-4o Proof:

```
 { split; [|basic_solver].
unfold col.
rewrite wf_coE, wf_coD.
basic_solver. }
```

#### Theorem name: 
#### `sw_covered`

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite covered_in_coverable at 1.
rewrite (dom_rel_helper dom_sw_coverable).
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `iord_irreflexive`

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold iord.
iord_dom_unfolder.
{
eapply sb_sc_acyclic; eauto.
apply CONS.
}
eapply ar_rf_ppo_loc_acyclic; eauto.
 }
```

#### Theorem name: 
#### `cr_hb_cr_hb`

#### OpenAI GPT-3.5 Proof:

```
 { 
rewrite crE; relsf.
split; try basic_solver.
unfolder; ins; desf; vauto.
 }
```

#### Theorem name: 
#### `dom_rfe_acq_sb_issuable`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `t_acq_covered`

#### Tactician Proof:

```
 { synth. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ar_rf_ppo_loc_ct_issuable_in_I`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `dom_wex_sb_issued`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rfi_rmw_in_sb_loc`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `init_ninit_sb`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `IPROP_in_iord_simpl`

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `dom_rfe_acq_sb_issued`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ar_rfrmw_ct_CI_in_I`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `w_hb_loc_r_in_co_rf`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `init_exec_tls_disjoint`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sim_execution_same_acts`

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `bob_in_ar`

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `rfrmw_in_im_co`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sc_scb_pscb`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `fr_co`

#### CoqHammer Proof:

```
 { hammer. }
```

### Group B

#### Theorem name: 
#### `same_lab_u2v_dom_inclusion`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### OpenAI GPT-4o Proof:

```
 { unfold same_lab_u2v_dom.
ins.
apply S1. apply SS. auto. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
red; ins; eapply S1; eauto.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `s_imm_consistentimplies_c11_consistent`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `dom_ar_ct_issuable`

#### Anthropic Claude Proof:

```
 { 
by apply ar_ct_issuable_in_I.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
arewrite (ar ⊆ ar ∪ rf ⨾ ppo ∩ same_loc).
by unfold issuable; basic_solver 20.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sub_SB`

#### Anthropic Claude Proof:

```
 { unfold SB. 
rewrite sub_sb_in.
rewrite sub_sc_in. 
basic_solver 10. }
```

#### OpenAI GPT-4o Proof:

```
 { unfold SB.
rewrite sub_sb_in, sub_sc_in.
easy. }
```

#### Theorem name: 
#### `wf_ci0E`

#### Anthropic Claude Proof:

```
 {  
split; [|basic_solver].
unfold ci0.
rewrite (wf_ctrliE WF) at 1.  
rewrite (wf_detourE WF) at 1.
basic_solver 42.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold ci0.
rewrite (wf_ctrliE WF) at 1.
rewrite (wf_detourE WF) at 1.
basic_solver 42.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold ci0.
rewrite (wf_ctrliE WF) at 1.
rewrite (wf_detourE WF) at 1.
basic_solver 42.
 }
```

#### Theorem name: 
#### `issued_eq_ta_issue`

#### Anthropic Claude Proof:

```
 {  
unfold issued.
unfolder.
split; ins; desf; eexists (_, _); splits; ins; eauto.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold issued.
split; basic_solver.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold issued.
basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `FWBOB_trans`

#### Anthropic Claude Proof:

```
 { 
unfold "FWBOB".
apply transitiveI.  
iord_dom_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `depf_preserves_set_lexpr`

#### Anthropic Claude Proof:

```
 { 
induction expr; unfold DepsFile.lexpr_deps, DepsFile.val_deps; desf; apply AA.
 }
```

#### OpenAI GPT-4o Proof:

```
 { induction expr.
all: unfold DepsFile.lexpr_deps, DepsFile.val_deps in *; desf; eauto. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
  ins.
  induction expr; simpls.
  all: unfold DepsFile.lexpr_deps, DepsFile.val_deps; desf; try apply AA; try basic_solver.
  all: rewrite AA.
  all: basic_solver.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `wf_fwbobE`

#### Anthropic Claude Proof:

```
 { 
unfold fwbob.
rewrite wf_sbE.
basic_solver 42.
 }
```

#### Theorem name: 
#### `wf_hbD`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold hb.
rewrite (wf_ppoD WF) at 1.
rewrite (wf_fenceD WF) at 1.
rewrite (wf_rfeD WF) at 1.
basic_solver 42.
 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold hb.
rewrite (wf_ppoD WF) at 1.
rewrite (wf_fenceD WF) at 1.
rewrite (wf_rfeD WF) at 1.
basic_solver 42.
 }
```

#### Theorem name: 
#### `wf_S_tmrD`

#### OpenAI GPT-4o Proof:

```
 { 
unfold S_tmr.
split; [basic_solver 21|].
rewrite !seqA.
arewrite_id ⦗W_ l⦘.
basic_solver 21.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold S_tmr; basic_solver 21.
 }
```

#### Theorem name: 
#### `urr_alt`

#### OpenAI GPT-4o Proof:

```
 { unfold urr.
split.
- generalize (@hb_trans G); basic_solver 21.
- rewrite (wf_scD WF_SC); generalize (@hb_trans G); basic_solver 21. }
```

#### Theorem name: 
#### `same_lab_u2v_dom_trans`

#### OpenAI GPT-4o Proof:

```
 { 
red.
ins.
specialize (S1 e EE).
specialize (S2 e EE).
by apply same_label_u2v_trans with (lbl2 := lab2 e).

 }
```

#### Theorem name: 
#### `tid_n_init_ext_sb`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite tid_ext_sb.
basic_solver.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sim_clos_empty`

#### OpenAI GPT-4o Proof:

```
 { unfold sim_clos.
unfold rel_clos, rmw_clos.
unfold covered, issued.
rewrite !set_pair_alt.
basic_solver. }
```

#### Theorem name: 
#### `sim_clos_dist`

#### OpenAI GPT-4o Proof:

```
 { unfold sim_clos.
rewrite rel_clos_dist, rmw_clos_dist.
basic_solver. }
```

#### OpenAI GPT-3.5 Proof:

```
 { unfold sim_clos.
rewrite !rmw_clos_dist, !rel_clos_dist.
basic_solver. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `wf_addrE`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
arewrite (addr ⊆ addr ∩ addr) at 1.
rewrite (addr_in_sb WF) at 1.
rewrite wf_sbE.
basic_solver.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
arewrite (addr ⊆ addr ∩ addr) at 1.
rewrite (addr_in_sb WF) at 1.
rewrite wf_sbE at 1.
basic_solver.
 }
```

#### Theorem name: 
#### `wf_depsD`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold Execution.deps.
rewrite (wf_dataD WF) at 1.
rewrite (wf_addrD WF) at 1.
rewrite (wf_ctrlD WF) at 1.
basic_solver 21.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold deps.
rewrite (wf_dataD WF) at 1.
rewrite (wf_ctrlD WF) at 1.
rewrite (wf_addrD WF) at 1.
basic_solver.
 }
```

#### Theorem name: 
#### `same_tid_trans`

#### OpenAI GPT-4o Proof:

```
 { unfold transitive.
unfold same_tid.
intros x y z Hxy Hyz.
unfold tid in *.
lia. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold transitive; intros x y z Hxy Hyz.
unfold same_tid in *; desf; congruence.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `wf_cc0D`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold cc0.
rewrite wf_dataD at 1; try done.
rewrite wf_addrD at 1; try done.
rewrite wf_ctrlD at 1; try done.
rewrite wf_sbE at 1; try done.
basic_solver 42.

 }
```

#### Theorem name: 
#### `issued_is_ta_propagate_to_G`

#### OpenAI GPT-4o Proof:

```
 { unfold issued, is_ta_propagate_to_G.
unfolder; split; ins; desf.
destruct y; ins; desf. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold issued, is_ta_propagate_to_G.
unfolder; split; ins; desf.
destruct y; ins; desf.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `covered_ta_reserve`

#### OpenAI GPT-4o Proof:

```
 { 
unfold covered.
unfolder.
split; ins; desf.
destruct y; ins.
desf.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold covered.
unfold acts_set.
unfolder; split; ins; desf.
destruct y; ins.
desf.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `wf_ar_rfrmwE`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold ar.
rewrite (wf_rfeE WF), (wf_ar_intE WF), (wf_scE WF_SC).
rewrite (wf_rfE WF), (wf_rmwE WF).
basic_solver 42.

 }
```

#### Theorem name: 
#### `eSB_in_sb_sc_ct`

#### OpenAI GPT-4o Proof:

```
 { 
unfold "SB".
clear.
basic_solver 10.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ar_rf_ppo_loc_rt_I_in_I`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite rtE, !seq_union_l, !seq_union_r, seq_id_l, dom_union.
unionL; [basic_solver|].
apply ar_rf_ppo_loc_ct_I_in_I.
 }
```

#### Theorem name: 
#### `ar_rt_I_in_I`

#### OpenAI GPT-4o Proof:

```
 { rewrite rtE.
rewrite !seq_union_l, !seq_union_r, dom_union; unionL.
{ basic_solver. }
apply ar_ct_I_in_I. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `otc_dr_ppo_I`

#### OpenAI GPT-4o Proof:

```
 { 
etransitivity.
2: by apply otc_dr_pb_I; auto.
basic_solver 10.

 }
```

#### Theorem name: 
#### `TWF_helper_rmw`

#### OpenAI GPT-4o Proof:

```
 { red in TWF.
intro H.
specialize (TWF (ThreadEvent tid (eindex s1 + 1)) H).
desf.
lia. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
red in TWF.
intro.
specialize (TWF (ThreadEvent tid (eindex s1 + 1)) H); desf.
lia.
 }
```

#### Theorem name: 
#### `wf_bobE`

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold bob.
rewrite wf_fwbobE; auto.
rewrite wf_sbE; auto.
basic_solver.

 }
```

#### Theorem name: 
#### `wf_fenceD`

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold fence.
rewrite (wf_syncD WF) at 1.
rewrite (wf_lwsyncD WF) at 1.
basic_solver 42.
 }
```

#### Theorem name: 
#### `deps_in_ctrl_or_dob`

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold deps, ctrl, dob.
rewrite (wf_dataE WF) at 1.
rewrite (wf_addrE WF) at 1.
rewrite (wf_ctrlE WF) at 1.
basic_solver 12.
 }
```

#### Theorem name: 
#### `rmw_in_ppo`

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold ppo; rewrite (wf_rmwD WF) at 1; hahn_frame.
econs; basic_solver 12.
 }
```

#### Theorem name: 
#### `ar_rt_CI_in_I`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `restrict_threads_bound`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `sub_IPROP`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ext_sb_semi_total_r`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `rmw_sb_W_in_ppo`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `coi_coe`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `dob_alt`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `tls_coherent_ext`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `col_trans`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `release_rf_rmw_steps`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `issuable_iord_dom_cond`

#### CoqHammer Proof:

```
 { hammer. }
```

#### Theorem name: 
#### `istep_eindex_shift`

#### CoqHammer Proof:

```
 { hammer. }
```

### Group C

#### Theorem name: 
#### `sb_f_at`

#### Predefined tactic Proof:

```
 { firstorder auto with *. }
```

#### Theorem name: 
#### `wf_ii0E`

#### Anthropic Claude Proof:

```
 { 
split; [|basic_solver].
unfold ii0.
rewrite (wf_addrE WF) at 1.
rewrite (wf_dataE WF) at 1.
rewrite (wf_rdwE WF) at 1.
rewrite (wf_rfiE WF) at 1. 
basic_solver 42.
 }
```

#### OpenAI GPT-4o Proof:

```
 { 
split; [|basic_solver].
unfold ii0.
rewrite (wf_addrE WF) at 1.
rewrite (wf_dataE WF) at 1.
rewrite (wf_rdwE WF) at 1.
rewrite (wf_rfiE WF) at 1.
basic_solver 42.

 }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
split; [|basic_solver].
unfold ii0.
sin_rewrite (wf_addrE WF).
sin_rewrite (wf_dataE WF).
sin_rewrite (wf_rdwE WF).
sin_rewrite (wf_rfiE WF).
basic_solver 42.
 }
```

#### Theorem name: 
#### `step_threads_set`

#### Anthropic Claude Proof:

```
 { 
destruct STEP as [ll STEP].
cdes STEP.
destruct ISTEP0.
all: rewrite UG.
all: split.
1,2: unfold add, add_rmw; simpls; basic_solver 10.
all: unfold add; simpls; basic_solver 10.
all: unfold add_rmw; simpls; basic_solver 10.
all: basic_solver.
 }
```

#### Theorem name: 
#### `is_r_increasing`

#### Anthropic Claude Proof:

```
 { 
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done. 
all: unfold add, add_rmw, is_r; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
 }
```

#### OpenAI GPT-4o Proof:

```
 { destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_r; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone). }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
destruct STEP; desc.
red in H; desc.
destruct ISTEP0.
all: rewrite UG; try done.
all: unfold add, add_rmw, is_r; ins.
all: unfolder; ins; desc; eauto.
all: rewrite !updo; try done.
all: try by (intro; subst; eapply TWF_helper; edone).
all: try by (intro; subst; eapply TWF_helper_rmw; edone).
 }
```

#### Theorem name: 
#### `tlsc_I_in_W`

#### Anthropic Claude Proof:

```
 { 
apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
rewrite TC', set_inter_union_l.  
apply set_subset_union_l.
split.
{
etransitivity; [red; intro; apply proj1| ].  
unfold init_tls.
erewrite set_pair_alt, init_w; eauto.
basic_solver.
}
rewrite INE.
unfold exec_tls.
rewrite !set_pair_alt.
unfold action, event. 
unfolder.
ins; desf; congruence.
 }
```

#### OpenAI GPT-4o Proof:

```
 { apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
rewrite TC', set_inter_union_l.
apply set_subset_union_l.
split.
{
  etransitivity; [red; intro; apply proj1| ].
  unfold init_tls.
  erewrite set_pair_alt, init_w; eauto.
  basic_solver.
}
rewrite INE.
unfold exec_tls.
rewrite !set_pair_alt.
unfold action, event.
unfolder.
ins; desf; congruence. }
```

#### OpenAI GPT-3.5 Proof:

```
 { 
apply tls_coherent_defs_equiv in TCOH as [tc' [INE TC']].
rewrite TC', set_inter_union_l.
apply set_subset_union_l.
split.
{
etransitivity; [red; intro; apply proj1| ].
unfold init_tls.
erewrite set_pair_alt, init_w; eauto.
basic_solver.
}
rewrite INE.
unfold exec_tls.
rewrite !set_pair_alt.
unfold action, event.
unfolder.
ins; desf; congruence.
 }
```

#### Theorem name: 
#### `F_Rel_eq`

#### Anthropic Claude Proof:

```
 { unfold G', relax_release_labels. 
unfold is_rel, is_f, Events.mod.
ins.
unfolder.
split; ins; desf; splits; auto.
all: try by intro; desf; type_solver. }
```

#### OpenAI GPT-4o Proof:

```
 { 
unfold G', relax_release_labels, is_f, is_rel, Events.mod; ins.
unfolder; split; ins; desf; splits; eauto.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `t_rel_other_thread`

#### OpenAI GPT-4o Proof:

```
 { unfold t_rel, c_rel.
rewrite <- !id_inter.
rewrite !set_inter_union_l.
arewrite (Init ∩₁ C ≡₁ Init ∩₁ C').
{
  split; [basic_solver|].
  rewrite CE.
  generalize CINIT.
  basic_solver.
}
basic_solver 21. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `ar_C_in_CI`

#### OpenAI GPT-4o Proof:

```
 { 
rewrite covered_in_coverable at 1; eauto.
apply ar_coverable_in_CI.
 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `dom_rel_collect_event`

#### OpenAI GPT-4o Proof:

```
 { rewrite <- AA.
unfolder.
ins.
desf.
exists (mkTL b x).
unfolder.
splits; eauto. }
```

#### Theorem name: 
#### `issued_ta_issue`

#### OpenAI GPT-4o Proof:

```
 { 
unfold issued.
unfolder; split; ins; desf.
{
destruct y; ins.
desf.
}
eexists (_, _).
splits; ins; eauto.

 }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `issued_EW`

#### OpenAI GPT-4o Proof:

```
 { unfold issued.
apply set_subset_inter_r; split.
- apply issuedE; auto.
- apply issuedW; auto. }
```

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `iord_exec_tls_cip`

#### OpenAI GPT-4o Proof:

```
 { rewrite restr_relE.
apply dom_helper_3.
unfold exec_tls_cip, exec_tls.
rewrite !set_pair_alt.
rewrite set_interC with (s' := W), set_map_inter, <- set_interA.
rewrite <- set_inter_union_l.
rewrite restr_rel_cross_inter.
apply restr_rel_mori; [basic_solver| ].
iord_parts_unfolder.
repeat apply inclusion_union_l; try basic_solver.
all: unfolder; ins; destruct x, y; ins; desc; subst; intuition. }
```

#### Theorem name: 
#### `isim_trav_step_new_issued_tid`

#### OpenAI GPT-4o Proof:

```
 { 
assert (issued TC ⊆₁ issued TC ∩₁ NTid_ thread ∪₁ issued TC ∩₁ Tid_ thread) as BB.
{
apply ntid_tid_set_inter.
}
assert (sim_trav_step G sc TC TC') as ST by (eexists; eauto).
split.
2: {
rewrite sim_trav_step_issued_le with (C':=TC'); eauto.
basic_solver.
}
inv ITV; simpls; unionL.
all: try (rewrite BB at 1; basic_solver 10).
all: try basic_solver 10.
all: try (apply (wf_rmwt WF) in RMW; rewrite RMW).
all: basic_solver 10.

 }
```

#### Theorem name: 
#### `reserved_ta_reserve`

#### OpenAI GPT-3.5 Proof:

```
 { 
unfold reserved.
unfolder; split; ins; desf.
{
destruct y; ins.
desf.
}
eexists (_, _).
splits; ins; eauto.
 }
```

#### Theorem name: 
#### `rel_clos_idemp`

#### Tactician Proof:

```
 { synth. }
```

#### Theorem name: 
#### `dom_sb_W_rel_issued`

#### Tactician Proof:

```
 { synth. }
```
