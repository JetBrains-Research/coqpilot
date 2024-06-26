# Experiments Report

We have conducted several experiments using the [imm project](https://github.com/weakmemory/imm). In this report we tell about the process of data preparations, used methods, conducted experiments, and their detailed results.

## Update: 10-06-2024

We have found a critical bug in the checker of proofs, which caused false positive results in a few cases in the experiment. The data below was corrected and updated.

## Data Preparation

 We measured the performance of our solution on three groups of theorems. Grouping was done on the basis of length of human-written proofs measured in proof steps. Also the groups sizes were chosen with respect to the distribution of proofs lengths in the imm project. We have considered the theorems with proofs length in the interval $[3; 20]$. Such theorems amount to 83% of proofs from the imm project. We have randomly chosen theorems for each group. As the result we got 45 thereoms divided into the following groups:

| Group | Length Interval | Size |
|----------|----------|----------|
| A | 3 – 4   | 20 |
| B | 5 – 8   | 14 |
| C | 9 – 20  | 11 |

The list of the chosen theorems divided by groups you can find in the table provided in the [Results](#results) section.

## Methods

In our experiments we compared different methods which can be used by CoqPilot:  Predefined tactic (`firstorder auto with *.`), OpenAI GPT-4, OpenAI GPT-3.5, LLaMA-2 13B Chat, Anthropic Claude. We have used following parameters for each of the models:

### OpenAI GPT-4 

```
{
    modelName: "openai-gpt-4",
    choices: 20,

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

In the table below you can find the results of our experiments. For each of the theorems we show its group  and the methods which proved the theorem during our experiments.


| Group | File | Theorem Name | Predefined tactic | OpenAI GPT-4 | OpenAI GPT-3.5 | LLaMA-2 13B Chat | Anthropic Claude | 
|-------|------|--------------|-------------------|--------------|----------------|------------------|------------------|
| A | [basic/Execution_eco.v](https://github.com/weakmemory/imm/blob/master/src/basic/Execution_eco.v) | `rf_rmw_ct_in_co`| &#x2717; | [&#x2713;](#rf_rmw_ct_in_co) |  &#x2717; | &#x2717; | &#x2717; |
| A | [imm/imm_hb.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_hb.v) | `cr_hb_hb`| &#x2717; | [&#x2713;](#cr_hb_hb) | [&#x2713;](#cr_hb_hb) | &#x2717; | [&#x2713;](#cr_hb_hb) |
| A | [basic/FinExecution.v](https://github.com/weakmemory/imm/blob/master/src/basic/FinExecution.v) | `fin_exec_same_events`| [&#x2713;](#fin_exec_same_events) | [&#x2713;](#fin_exec_same_events) | [&#x2713;](#fin_exec_same_events) | &#x2717; | [&#x2713;](#fin_exec_same_events) |
| A | [basic/Execution.v](https://github.com/weakmemory/imm/blob/master/src/basic/Execution.v) | `sb_trans`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [basic/Execution.v](https://github.com/weakmemory/imm/blob/master/src/basic/Execution.v) | `sb_same_loc_W_trans`| &#x2717; | [&#x2713;](#sb_same_loc_w_trans) | &#x2717; | &#x2717; | &#x2717; |
| A | [basic/Events.v](https://github.com/weakmemory/imm/blob/master/src/basic/Events.v) | `restr_eq_rel_same_loc`| [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) | [&#x2713;](#restr_eq_rel_same_loc) |
| A | [basic/Events.v](https://github.com/weakmemory/imm/blob/master/src/basic/Events.v) | `same_loc_loceq`| [&#x2713;](#same_loc_loceq) | [&#x2713;](#same_loc_loceq) | [&#x2713;](#same_loc_loceq) | &#x2717; | &#x2717; |
| A | [traversal/TraversalConfigAltOld.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfigAltOld.v) | `otc_I_ar_rfrmw_I_implied_helper_2`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [simhelpers/CertCOhelper.v](https://github.com/weakmemory/imm/blob/master/src/simhelpers/CertCOhelper.v) | `wf_colD`| &#x2717; | [&#x2713;](#wf_cold) | [&#x2713;](#wf_cold) | &#x2717; | &#x2717; |
| A | [imm/SubExecution.v](https://github.com/weakmemory/imm/blob/master/src/imm/SubExecution.v) | `sub_rfe`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm/SubExecution.v](https://github.com/weakmemory/imm/blob/master/src/imm/SubExecution.v) | `sub_Rel`| &#x2717; | [&#x2713;](#sub_rel) | &#x2717; | &#x2717; | &#x2717; |
| A | [imm/imm_s.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_s.v) | `wf_rfirmwsf`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [traversal/TraversalConfig.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfig.v) | `issuableW`| [&#x2713;](#issuablew) | &#x2717; | [&#x2713;](#issuablew) | &#x2717; | [&#x2713;](#issuablew) |
| A | [traversal/TraversalConfig.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfig.v) | `w_coverable_issued`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [traversal/TraversalConfig.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfig.v) | `ar_rfrmw_rt_CI_in_I`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [hardware/imm_sToARM.v](https://github.com/weakmemory/imm/blob/master/src/hardware/imm_sToARM.v) | `WF`| [&#x2713;](#wf) | [&#x2713;](#wf) | &#x2717; | &#x2717; | [&#x2713;](#wf) |
| A | [travorder/TraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TraversalOrder.v) | `FWBOBFWBOB`| &#x2717; | [&#x2713;](#fwbobfwbob) | &#x2717; | &#x2717; | &#x2717; |
| A | [travorder/EventsTraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/EventsTraversalOrder.v) | `dom_rfe_acq_sb_issued`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [travorder/EventsTraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/EventsTraversalOrder.v) | `rfrmw_coverable_in_I`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| A | [imm/imm_s_hb.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_s_hb.v) | `hb_trans`| &#x2717; | [&#x2713;](#hb_trans) | [&#x2713;](#hb_trans) | &#x2717; | &#x2717; |
| B | [travorder/TraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TraversalOrder.v) | `set_pair_cancel_action`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [travorder/TraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TraversalOrder.v) | `event_issue_finite_inj`| &#x2717; | [&#x2713;](#event_issue_finite_inj) | [&#x2713;](#event_issue_finite_inj) | &#x2717; | &#x2717; |
| B | [basic/ProgToExecutionProperties.v](https://github.com/weakmemory/imm/blob/master/src/basic/ProgToExecutionProperties.v) | `ectrl_increasing`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm/Sc_opt.v](https://github.com/weakmemory/imm/blob/master/src/imm/Sc_opt.v) | `scb_in_hb_eco`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | [&#x2713;](#scb_in_hb_eco) |
| B | [travorder/TLSCoherency.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TLSCoherency.v) | `tls_coherent_ext_union`| [&#x2713;](#tls_coherent_ext_union) | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [ldrf/LDRF_Fsc.v](https://github.com/weakmemory/imm/blob/master/src/ldrf/LDRF_Fsc.v) | `RFE1`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm/imm_hb.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_hb.v) | `wf_swD`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm/imm_s_ppo.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_s_ppo.v) | `ar_int_rfe_ct_rfrmw_rt_in_ar_int_rfe_ct`| &#x2717; | &#x2717; |  &#x2717; | &#x2717; | &#x2717; |
| B | [imm/CombRelations.v](https://github.com/weakmemory/imm/blob/master/src/imm/CombRelations.v) | `eco_furr_irr`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [imm/CombRelations.v](https://github.com/weakmemory/imm/blob/master/src/imm/CombRelations.v) | `urr_hb_sc_hb_irr`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [travorder/EventsTraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/EventsTraversalOrder.v) | `W_ar_coverable_issuable_in_CI`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [travorder/EventsTraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/EventsTraversalOrder.v) | `ar_coverable_in_CI`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [hardware/Power_fences.v](https://github.com/weakmemory/imm/blob/master/src/hardware/Power_fences.v) | `lwsync_sync`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| B | [basic/Execution_eco.v](https://github.com/weakmemory/imm/blob/master/src/basic/Execution_eco.v) | `eco_refl`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [imm/imm_common_more.v](https://github.com/weakmemory/imm/blob/master/src/imm/imm_common_more.v) | `W_sb_same_loc_detour`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [traversal/SimTraversalProperties.v](https://github.com/weakmemory/imm/blob/master/src/traversal/SimTraversalProperties.v) | `isim_trav_step_new_e_tid`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [travorder/EventsTraversalOrder.v](https://github.com/weakmemory/imm/blob/master/src/travorder/EventsTraversalOrder.v) | `rf_rmw_issued`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [basic/Execution.v](https://github.com/weakmemory/imm/blob/master/src/basic/Execution.v) | `rmw_non_init_lr`| &#x2717; | &#x2717; | [&#x2713;](#rmw_non_init_lr) | &#x2717; | &#x2717; |
| C | [ocamlmm/OCamlToimm_s.v](https://github.com/weakmemory/imm/blob/master/src/ocamlmm/OCamlToimm_s.v) | `wr_mode`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [ocamlmm/OCamlToimm_s.v](https://github.com/weakmemory/imm/blob/master/src/ocamlmm/OCamlToimm_s.v) | `sbnl_hb_scb`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [travorder/TLSCoherency.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TLSCoherency.v) | `iord_exec_tls`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [travorder/TlsViewRelHelpers.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TlsViewRelHelpers.v) | `t_acq_n_sc_fence_step`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [traversal/TraversalConfig.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfig.v) | `init_issued`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [traversal/TraversalConfig.v](https://github.com/weakmemory/imm/blob/master/src/traversal/TraversalConfig.v) | `dom_detour_rfe_ppo_issuable`| &#x2717; | &#x2717; | &#x2717; | &#x2717; | &#x2717; |
| C | [travorder/TlsEventSets.v](https://github.com/weakmemory/imm/blob/master/src/travorder/TlsEventSets.v) | `issued_ta_issue`| &#x2717; | [&#x2713;](#issued_ta_issue) | [&#x2713;](#issued_ta_issue) | &#x2717; | &#x2717; |



## Generated Proofs

Here you can find the generated proofs for each of proved theorems during the experiments.

### Group A

#### Theorem name: 
#### `rf_rmw_ct_in_co`


#### OpenAI GPT-4 Proof:

```
rewrite (rf_rmw_in_co WF SC_PER_LOC) at 1.
apply (ct_of_trans (co_trans WF)).
```

#### Theorem name: 
#### `cr_hb_hb`

#### OpenAI GPT-4 Proof:

    generalize hb_trans; basic_solver 10.

#### OpenAI GPT-3.5 Proof:

    split; [|basic_solver].
    unfold hb; rewrite ct_end at 1; rels.

#### Claude Proof:

    generalize hb_trans; basic_solver 10.


#### Theorem name: 
#### `fin_exec_same_events`

#### Firstorder tactic Proof:

    firstorder auto with *.

#### OpenAI GPT-4 Proof:

    red in FIN.
    red.
    rewrite <- SAME.
    apply FIN.

#### OpenAI GPT-3.5 Proof:

    unfold fin_exec in *.
    rewrite <-SAME in *.
    intuition.

#### Claude Proof:

    unfold fin_exec in *.
    intros.
    rewrite <- SAME.
    apply FIN.



#### Theorem name: 
#### `sb_same_loc_W_trans`

#### OpenAI GPT-4 Proof:

    unfold Events.same_loc.
    unfolder; ins; desf; eauto.
    splits; auto.
    generalize sb_trans; basic_solver 21.
    congruence.

#### Theorem name: 
#### `restr_eq_rel_same_loc`

#### Firstorder tactic Proof:

    firstorder auto with *.

#### OpenAI GPT-4 Proof:

    unfolder; split; ins; desf; splits; auto.

#### OpenAI GPT-3.5 Proof:

    unfold restr_eq_rel, same_loc; basic_solver.

#### LLaMA Proof:

    unfold same_loc; basic_solver.

#### Claude Proof:

    unfold same_loc; basic_solver.

#### Theorem name: 
#### `same_loc_loceq`

#### Firstorder tactic Proof:

    firstorder auto with *.

#### OpenAI GPT-4 Proof:

    unfold same_loc; unfolder; firstorder.

#### OpenAI GPT-3.5 Proof:

    unfold funeq, same_loc; firstorder.

#### Theorem name: 
#### `wf_colD`
#### OpenAI GPT-4 Proof:
    apply dom_helper_3.
    unfold col; rewrite wf_coD; basic_solver.
#### OpenAI GPT-3.5 Proof:
    unfold col; split; [|basic_solver].
    rewrite wf_coD.
    unfold Events.same_loc; unfolder; ins; desf; eauto.

#### Theorem name:  
#### `sub_Rel`
#### OpenAI GPT-4 Proof:
    by rewrite (sub_lab SUB).


#### Theorem name:  
#### `issuableW`
#### Firstorder tactic Proof:
    firstorder auto with *.
#### OpenAI GPT-3.5 Proof:
    unfold issuable.
    basic_solver.
#### Claude Proof:
    unfold issuable.
    basic_solver.

#### Theorem name:  
#### `WF`
#### Firstorder tactic Proof:
    firstorder auto with *.
#### OpenAI GPT-4 Proof:
    by apply CON.
#### Claude Proof:
    apply CON.

#### Theorem name:  
#### `FWBOBFWBOB`
#### OpenAI GPT-4 Proof:
    iord_dom_solver.

#### Theorem name: 
#### `hb_trans`
#### OpenAI GPT-4 Proof:
    unfold hb; apply transitive_ct.
#### OpenAI GPT-3.5 Proof:
    unfold hb.
    apply transitive_ct.

### Group B

#### Theorem name: 
#### `event_issue_finite_inj`

#### OpenAI GPT-4 Proof:

    exists [mkTL ta_issue y]; ins; desf.
    red in IN0; destruct x as [[]]; ins; auto.

#### OpenAI GPT-3.5 Proof:

    exists [mkTL ta_issue y].
    ins.
    desf.
    red in IN0.
    destruct x as [[]]; ins; auto.

#### Theorem name: 
#### `tls_coherent_ext_union`

#### Firstorder tactic Proof:
    firstorder auto with *.

#### Theorem name: 
#### `scb_in_hb_eco`

#### Claude Proof:

    unfold imm.scb.
    rewrite sb_in_hb, co_in_eco, fr_in_eco. 
    arewrite (hb ∪ (hb \ same_loc) ⨾ hb ⨾ (hb \ same_loc) ∪ hb ∩ same_loc ⊆ hb).
    {
      generalize (@hb_trans G).
      basic_solver.
    }
    arewrite (hb ∪ eco ∪ eco ⊆ hb ∪ eco).
    basic_solver.

### Group C

#### Theorem name: 
#### `rmw_non_init_lr`

#### OpenAI GPT-4 Proof:

    split; [|basic_solver].
    rewrite (rmw_from_non_init WF) at 1.
    rewrite <- seqA.
    apply codom_rel_helper.
    rewrite (rmw_in_sb WF).
    clear; rewrite no_sb_to_init; basic_solver.

#### Theorem name: 
#### `issued_ta_issue`

#### OpenAI GPT-3.5 Proof:

    unfold issued.
    unfolder; split; ins; desf.
    {
    destruct y; ins.
    desf.
    }
    eexists (_, _).
    splits; ins; eauto.

#### OpenAI GPT-4 Proof:

    unfold issued.
    unfolder; split; ins; desf.
    {
    destruct y; ins; desf.
    }
    by eexists (_, _); splits; ins.



<!-- TODO: reference to the the results in abstract? -->