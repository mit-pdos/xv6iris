# LB/AxSL agent primer (read this INSTEAD of durable-notes/README/the design doc)

> **Lean port in progress:** the weak-memory development is being ported to Lean on bookmark `weak` (see [`notes/weak-port-map.md`](../../notes/weak-port-map.md)); file/tactic names below are Rocq ([`claude-notes/LEAN.md`](../../claude-notes/LEAN.md)).

Scope: proof work on `iris/Ax*.v` (LB via an AxSL-style base logic over RVWMO). Design:
`design/weak-memory-lb-axsl.md` (read only the § your task names). Tracker/status:
`projects/weak-memory-lb-axsl.md`. File headers are authoritative and usually carry a FINDING/
RESIDUALS block; read a file's first ~40 lines + `tools/outline`, never the whole file.

## 1. File map (main entry lemmas in [brackets])
Base logic (pure graph + opsem + WP)
- AxGraph: gob, grf_at, owned-read lemma over RVWMO⁻ [ob_sub_gmo, owned_read, own_forward].
- AxGraphCat: faithful riscv.cat ppo incl. rule 12, model `rvwmo_cat_consistent`, gob_cat, §7 tie vocab
  [minus_implies_cat, ob_cat_sub_gmo, owned_read_cat, tie_inv/tie_read_i/ii].
- AxGraphDec [cat_consistent_b_sound] (verdict = vm_compute); AxGraphWit (fwd/rel/cyc/str), AxLitmus, AxTieProc.
- AxDeps: tagged deps (addr/data vs ctrl/trans/ctx), `gdexec_t`, `rvwmo_cat_consistent_t`, row_deps_t.
- AxGraphAgree: graph_agree pins GD'=GD at skel_axirisG (fix for "∀GD' in step case").
- AxOpsem: opax thread `athread`=(pexv6, row pos k); `astep_prog`/`astep`/`aread_step`/`awire`; AStepWrite
  checks stored bytes (`wl_wdata l = lbl_data lb`); AStepFetch; `OpaxWit` demo (wt_*).
- AxWp: `axirisG` interface, tied annotations `e ↦ₐ P` (Module AxAnnot inside AxWp: annot_alloc/detach/
  merge), `annot_interp`, `na_splitting_wf`, `|=i=>`, `post_lifting`, `flow_eq_dyn`, `wp_pre_step_def`
  (clauses a read / b step / c wire), `wp`, `wpc`, `graph_value`/`graph_data`, `eids_before`, skel_axirisG.
- AxWpD: `wpd` = wp with read arm PINNED to graph value (∀v, graph_value GD e = Some v -∗ …).
- AxWpDSteps: `astep_any_nf_gv`, `wpd_stepsN`, [wpd_step_annot, wpd_nsteps]. AxWpDHarts: [wpd_harts_nsteps].
- AxLifting: flow_eq_ea, ea_local_wf, [ea_local_wf_ev_step]. AxReadAll: demonic ∀v read [wp_read_step_all_wand].
- AxGate/AxGateWp/AxGateAdeq/AxGateAdeq2: ctrl gate [gate_store_after, wp_gate, na_pure_global].
- AxSymReg: symbolic register surface `r ↦ᵣ⟨x⟩` over unmodified SC leaf specs; AxSymLd [wp_ld8_forallv_ax].
- AxBridge (flat memory vs rf), AxPair (run pairing), AxInstr [wp_ainstr(_ld8/_sd8), AxInstrTargets class],
  AxInstrFacts [hwdat/hrdat(n)_spec_of_graph], AxRowConf [row_emitted_from_run(_sound)].
Protocol (L2 ownership)
- AxGhost: mono-log per byte, `hist_auth γ a q H` / `hist_snap γ a H` [owned_read_ghost].
- AxToken: owned_frac/owned, `tok_tie`, `tok_tied`, read/write rule statements.
- AxProt: `prot_inv γ GD s` as ob_st_interp [prot_inv_prefix_cov/_write_step/_read_step, flow_eq_owned_read_byte].
- AxProtInst (axprot_pol: gco-pred handout), AxProtCov/Cov2/Cov3 (C6 coverage; [axprot_adequate_ghost]),
  AxCov/AxCovMono/AxCovClose (class_epoch_gmo_mono, open/argued), AxProtGate [gate_delivers_expected_fwd],
  AxProtGateN (n-byte gate), AxProtBytes (n-byte: `tokn a Hs S`, wp_write_owned_tokn, writen-snap lemmas).
Adequacy
- AxAdequacy [adequacy_ord] (phase 1 + gmo phase 2), AxAdequacyL [adequacy_ord_L over pred-closed L,
  axpol_wf_L_of_pred_closed_flow], AxAdequacyChk (wpc, [adequate_chk_adequate]).
- AxSched (joint gmo scheduler, [sched_correct, sched_terminates]), AxSchedIris (Iris shell),
  AxSchedGD [sched_proc_adequate, sched_L_pred_closed_flow]. AxRunGV/AxRunGV2 [run_at_graph_values_*,
  hemit_run_at_graph_values].
- AxTierA (TRIVIAL skeleton), AxTierA2 [AxGA2 record, sched_gatefree_run, tierA_adequacy_ann],
  AxTierA3 [tierA_adequacy_ann_gmo, tierA_adequacy_ann_dev2] ← the adequacy theorem to use.
  AxTierA4 [tierA_adequacy_ann_run: ANY completed sched run with axpol_wf_L; the gate-free RUN restriction was
  irrelevant — the real restriction is POLICY (handouts gmo-earlier); sched_no_fwd/fwd_pol_unrealizable].
  AxSchedSH [InvSH: deferred read e1, gpo∧gmo_lt ⇒ processed first; sched_axpol_wf_proc_dev2], AxSchedFwd [NEGATIVE:
  a forwarded reload is processed BEFORE its po-earlier store on every run], AxFwdSource [rfi_fwd_source, epi_reload_fwd:
  forwarding is a PURE graph fact], AxAllHarts [tierA_adequacy_all(_harts)(_run): all 8 CPUs + opaque device agents,
  framed_wpd, wpd_idle], AxWpcAdeq [wpc_adequacy_ann_run/_gmo: wpc = AxSL checkpointed WP, not crash WP],
  AxViol [gviolation_hart (K1 graph restatement), owned_no_violation from timeline gtl_ok, gviolation_sat].
Lock slice (abstract rows unless noted)
- Graph: AxLockGraph [x_writes_gmo_before_read(_genesis), greads_byte_no_visible_write_is_image],
  AxLockSerial [cs_serialized, cs_owned_write, cs_handoff_last].
- Protocol: AxProtLock (prot_inv_lock', tok_retie_ob), AxProtLock2 (prot_inv_lock'', ∀σ-robust flow eqs),
  AxProtLock3 (genesis, lock_axpol, lock_Hob_alloc). AxLockOwn [lock_read_own(_genesis)].
- WP: AxLockWp/Wp2 (wp), AxLockWpD [wpd_release_store, wpd_amoswap_aq_lob].
- Old Prop results (mostly VACUOUS/TRIVIAL, headers say so): AxLockSlice, AxLockAdeq [lock_slice_sound''],
  AxLockWitness [race4_sound], AxLockRace/Race2/Race3 [..._VACUOUS], AxLockGen, AxLockN/N2/N3, AxLockMutex(2),
  AxLock3 [lock3s_sound], AxLockSmell.
- Tier-A lock3s (current): AxLock3Prog (hand pexv6 rows l3p_w_row/l3p_r_row), AxLock3Wp/Wp2/Wp3,
  AxLock3Writer [wpd_writer_hart(_rel)], AxLock3Reader [wpd_reader_hart(_rel)], AxLock3Thm
  [lock3s_dichotomy, lock3s_verified, lock3s_value], AxLock3Cert [lock3s_cert_AB/BA],
  AxLock3Race [race_wpd_unprovable, race_c_wpd_trivial]. AxSlice = empty stub.
Fetch / Sail bridge
- AxFetch (4.9k lines, PURE): real Sail row runs [af_ld8_run_to_read, af_ld8_row_run, af_sd8_row_run,
  af_jalr_row_run, af_cjr_row_run, af_csdsp_row_run, af_cldsp_row_run('), af_cjr_epilogue_gate_srcs'].
- AxRegOnly [af_ret_to_next_fetch, af_regonly_row_run]; AxStepDet [pnode_step_det] (nondet only at Ret-tick,
  Choose); AxWpdLift [wpd_of_closed_run(_maybe), closed_of_det_run]; AxRunClose [run_close_hclos/hwire/
  hnord, wpd_of_run_maybe]; AxCjrWpd [epure_gstep_rtc, wpd_fetch_step, wpd_fetch_then_run];
  AxBoundaryWpd [erun_gstep_to_memread, wpd_boundary_erd]; AxLdspWpd [wpd_load_step, ldsp_flow_owned,
  wpd_cldsp_from_fetch, wpd_ldsp_owned_ga2].
Epilogue (older, Prop-free): AxEpilogue [epilogue_ret_target_*], AxEpiShape, AxEpiChain
  [epilogue_consecutive_ret_own; cold ≈410s], AxEpiSat [epi_sat].
Epilogue J0 (concrete instance, vm_compute ledgers; hart state `AxEpiProbe.t_at pc`, `probe_regs`)
- AxEpiProbe: vm_compute through one concrete riscv_step (q* facts; post_fetch_seip_tick).
- AxEpiLedger: AxEpiModelFacts ledger, [wpd_cjr_step_of_ledger, epi_ledger_cjr, wpd_cjr_concrete];
  §5 c.ldsp [AxLdModelFacts, epi_ledger_cldsp, wpd_cldsp_concrete]. AxEpiLedgerSd [wpd_store_step,
  epi_ledger_csdsp, wpd_csdsp_concrete]. AxEpiLedgerTick [t_after_sd, wpd_cldsp_after_sd (∀ tick)].
- AxEpiChainSdLd [wpd_ret_boundary, wpd_past_row_end, wpd_epi_sd_ld]; AxEpiSdLdSat [gsdld, gsdld_sat].
- AxEpiOwned [store_flow_owned, wpd_epi_sd_ld_owned] (real protocol). AxEpiLdX1 [epi_ledger_cldsp_x1].
- AxEpiAdeq [epi_reload_sound] (pipeline milestone; TRIVIAL per AxEpiTrivial [epi_reload_trivial_1hart]).
- AxEpiRun: driver [node_step, drive, drive_sound, epi_reload_sound_gsdld] (fully closed).
- AxEpiRace2 [race2, race2_sat]; AxEpiRace2Run [race2_wpd_unprovable(_own), race2o_own_wpd];
  AxEpiSound2 [epi_reload_sound2] (ownership load-bearing); AxEpiSound3 [epi_reload_sound3] (hart 1 owns
  slot b); AxEpiTwinExact [race2x_own_wpd] (twin differs only in sp).
- AxEpiCjrSym [execute_JALR_s_eq, epi_ledger_cjr_sym, wpd_cjr_sym] (symbolic ra, tick=false only);
  AxEpiCjrFrame [erd_ag/epure_ag, wpd_cjr_frame_tick(_gen)] (any regfile agreeing on read footprint).
- AxEpiRetCert: `epi_ret_sound2_stmt` (Definition, NOT proved) + certs [race_ret_refutes_Hwp1,
  ok_ret_all_premises_and_concl]; `drive_bd`. AxEpiLdJr [12-case exact ld exit ld_out c w, wpd_cldsp_after_sd_exact,
  ld_out_x1, wpd_cjr_after_ld (both ticks)]. AxEpiRet (PARTIAL): [epi_ret_stmt_premises_reload, wpd_epi_ret_owned_rb];
  epi_ret_sound2 open (c.jr ledgers' row-end sets are BACKWARD closures). AxEpiSoundFwd [epi_reload_sound3_fwd: no
  Hlob_gmo — store forwarding covered; fwd_pol, fwd_load_flow; witness gsdld_fwd].

## 2. Architecture
- MAJOR DESIGN POINT (owner-accepted 2026-10-02, design §7.HI): resources moved between harts exist
  for the receiver only in PHASE 2 ⇒ phase-1 posts carry HANDLES (`c ↦ₐ (locked i c ∗ R c)`), owned
  points-to in critical sections are handle points-to `a ↦ₕ v` moved by owned load/store leaves along
  lobp. Never try to put a cross-hart resource in a WPd post "in hand" — it is impossible, not hard.
- Rev 7 (C0/C14): reads are DEMONIC (∀v; AxReadAll, AxWpD) — the owned fact is deposited as an ANNOTATION,
  not a pure hypothesis; the "ctrl gate" (RVWMO rule 11: stores after a branch/jump are gmo-after its load
  sources) lets the continuation at an LCtrl step learn the pure facts of the sources' annotations
  (AxGateWp.wp_gate; Hna from scheduler adequacy). Sequential code stays SC-like via AxSymReg's
  `r ↦ᵣ⟨x⟩ := ∃ v P, r ↦ v ∗ prov r = P ∗ (annots(P) ⇒ v = x)` over unmodified leaf specs (HARD REQUIREMENT).
- Protocol: `prot_inv γ GD s` is the axirisG `ob_st_interp`. Per-byte ghost logs `hist_auth γ a q H`
  (fractional, growth needs q=1) / `hist_snap γ a H` (persistent prefix). A write needs the full auth and
  extends the history; `tok_tie`/`tokn a Hs S` (n bytes) tie the token to graph events. Tokens travel between
  events through annotations `e ↦ₐ R` (write deposits, later read pulls with `annot_detach` as flow_in).
  Handout sets come from an `axpol` (s_pol, lobp); `na_splitting_wf`/`ea_local_wf` constrain locality.
- WPd (AxWpD): `WPd s @ st; i {{Φ}}`, clauses (a) read pinned to graph_value, (b) astep, (c) wire,
  (d) row-end: `at_k s = length row -∗ post_lifting Φ`. `post_lifting` gives Φ access to the annotation
  map na; the Prop result is READ BACK from an annotation at post_lifting (e.g. reload's `⌜v = sd_data⌝`).
- Adequacy: phase 1 runs every hart's WPd through ONE shared annot_interp (AxWpDHarts, no map unions);
  phase 2 processes events in scheduler order s_proc validating flow equations (AxSchedGD
  .sched_proc_adequate → AxAdequacyL). Use `AxTierA3.tierA_adequacy_ann_gmo`: s_pol/lobp ⊆ gmo-predecessors
  suffice, but ONLY on GATE-FREE runs (s_proc = gx_gmo); with deferred reads dev-2 edges need a new Inv clause.
  Premises: names N with `Hob_alloc ⊢ |==> ∃ nm σ0`, init resources as wand antecedents, run premise
  `run_at_graph_values`/`astep_any_nf_gv` (fetches are reads at graph_value, not AStepFetch).
- J0 ledger method: model facts are closed BOOLEAN equations at a concrete start state, discharged by
  `constructor; vm_compute; reflexivity`. Evaluators: `to_seip` (boundary prefix up to the one
  `RegRead sig_seip`, rv64d.v:17675), `erd` (erun stopping at first RAM read = fetch/load), `ewr` (twin
  stopping at RAM MemWrite), `WeakEvExecEff.epure D` (post-fetch certificate; sig_seip ∉ D ⇒ it IS a gstep
  run, AxCjrWpd.epure_gstep_rtc). Seip split: both answers of the bv 1 read are certified (lf_branch0/1).
  Tick: after `Ret` the hart runs `riscv_step tick` for EITHER tick (nondeterministic) ⇒ every non-first
  instruction needs tick=true too; tick=true reads sig_seip a 2nd time in tick_clock ⇒ split again
  (wpd_tick_tail). Composition: boundary → wpd_fetch_then_run → data step → Ret (wpd_ret_boundary).
- Driver (AxEpiRun): `node_step` = deterministic one-node step (regs answer from regfile incl. sig_seip,
  RAM reads take the row's value, writes must match row bytes, Ret continues with tick:=false); `drive`
  iterates to row end; `drive_sound` ⇒ `astep_any_nf_gv` run; one vm_compute discharges Hrun/Hend.
  `drive_bd` (AxEpiRetCert) continues to the next boundary. Driver failing = hart stuck (race2_hart1_stuck).

## 3. Idioms and pitfalls
- vm_compute on SYMBOLIC words blows up (bv_sign_extend/update_subrange/add_vec's bv_wrap; 11–16 GB).
  Fixes: `change_no_check` to a hand-written normal form, kernel checks at Qed (AxEpiLdX1); funext the body
  into a `_gen` with the stuck bit tests abstracted, replace by wrap-free twins, case-split the low bits of
  `ra = BV z pf` on positive constructors, then vm_compute per case (AxEpiCjrSym). Never vm_compute-compare
  two whole `mstate`s (regstate has no decidable eq; OOM) — pin by an exit set instead (AxEpiLedgerTick).
- Bitvector "Unable to unify 0%bv with 0%bv"-style failures that print identically (universe/implicit
  artifacts): go through a bool decision (`bv_eq`, `bool_decide` split) rather than reflexivity.
- Row-end obligations ONLY on the reachable invariant set (ledger_inv, epi_sd_ld_inv) plus a
  `*_inv_reaches_ret` sanity lemma — a ∀-states-at-position form is too strong for any meaningful Φ.
  Pin row length exactly (Hlen) or wpd_row_end_triv fires early. WPd@MaybeStuck is trivial for a stuck hart
  ⇒ pair with an ∃-run (driver) certificate.
- VACUITY is the #1 review finding. Every Prop result needs: a satisfiability witness discharging ALL
  premises on a concrete graph (AxEpiSdLdSat, AxLock3Cert, AxEpiRetCert ok_ret); for ownership claims a race
  witness where the premises-minus-WPd hold and the conclusion is false, plus a sanity twin whose WPd IS
  provable (race_c_wpd_trivial, race2x_own_wpd); `Print Assumptions` / check the CLOSED type
  (`Check (thm : False)` prints residual hyps). Red flags: `⊢ hist_auth γ a 1 []` as a Rocq hyp
  (refutable), premises ∀ over all axirisG instances, 1-hart results (trivial from gload_value), conclusion
  mentioning a free Vs instead of σ0.x1. Say TRIVIAL/VACUOUS/PIPELINE MILESTONE in the header when true.
- Section hygiene: `set_solver`/automation can drag unused section Context hyps into proof terms (e.g.
  AxProtBytes writen-snap lemmas carry an unused, likely-refutable Hrdatn_spec) ⇒ `Proof using …` + `clear`,
  nest sections so capstones carry only their real hyps, and check closed types.
- Stale dependency (rocq-check exit 2) ⇒ `--rebuild`. AxEpiLdJr is NOT in iris/_CoqProject (add in order
  when it lands; other AxEpi* are listed). AxEpiChain cold ≈410s, near the 570s check limit.
- `tools/rocq-query` replays the module's single-line `Require/Import` headers; multi-line Require lists
  (most Ax files) break it ⇒ pass modules with `-m AxFoo`.
- AxWp/AxOpsem are shared: build new rules as DERIVED lemmas in new files, don't edit definitions.

## 4. Check loop
- `tools/rocq-check FILE.v` — sync to the GCP build VM + `rocq-warm check`, compact verdict (0 ok, 1 fail,
  2 stale dep → `--rebuild`, 124 timeout 570s). `--compile` also writes the .vo (needed before downstream
  files/rocq-query see it). `ROCQ_CHECK_LINES=200` for more output.
- `tools/decl NAME` (local; `--proof`), `tools/outline FILE.v [PAT]`, `tools/rocq-query 'About X.'` (VM, fresh .vo).
- NEVER run coqc/make locally. Full build: `gcp-rocq/locked --proofs -k` (flock'd `run-on-gcp`; never a bare remote make).
