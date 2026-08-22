(** * WeakRvwmoCapstone.v — THE TIER-2 CAPSTONE, MODULO THE RESIDUE (B3)

    Design: [claude-notes/design/weak-memory-route-b.md] §0 (the goal) and
    §1 (the chain); worklist item B3 of the SEVENTH-PASS checkpoint in
    [claude-notes/projects/weak-memory-certification.md].

    ** THE THEOREM, IN WORDS.

    Take the booted xv6 machine state σ0 (a FRESH ERA: generation 0,
    powered, empty log, fresh views) and the EWP package the kernel proofs
    supply.  Then for EVERY graph [GD] that is

      - RVWMO⁻(+deps)-CONSISTENT ([rvwmo_minus_deps_consistent]), and
      - CONFORMANT to the xv6 image at the booted boot states
        ([gdexec_qconf boot d0 (img_z (wgimg σ0)) N]) —

    that graph is [RacyD]-ACYCLIC, it is REALIZED by a promise-free run of
    the event language from [(ep_init gen, σ0)] whose final log is the
    realizing candidate's own log, and — candidate-independently — EVERY
    reachable configuration of that language is violation-free and every
    thread of every reachable configuration is reducible.

    That is [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s conclusion, verbatim,
    reached from a GRAPH rather than from a hand-supplied sRVWMO candidate:
    tier 1 assumes the execution is already sRVWMO-consistent, tier 2
    assumes only that it is consistent for the WEAK declared model and
    derives the sRVWMO candidate.

    ** THE CHAIN (route-b §1), left to right through this file:

      G : gexec, [rvwmo_minus_deps_consistent] + [gdexec_qconf]
        │  T2-LIN — the induction on the event count, whose step is
        │  [cycle_kill]: no [RacyD] cycle at a conformant consistent graph
        │  all of whose proper hulls are already acyclic.  The step is
        │  discharged from the PER-SITE CLAIM [l2_claim] by
        │  [WeakRvwmoGlue2.cycle_kill_of_l2''] (segment-by-segment:
        │  graph-PINNED / CS-CHAINED / BAD, the last refuted by φ).
        ▼
      ∀ x, ¬ tc (RacyD GD) x x                    ([t2lin_of_cycle_kill])
        │  TOPO — [WeakRvwmoTopo.topo_supply] with [WeakRvwmoDec.racyD_dec]
        ▼
      G' : the normalized, rule-14 graph
        │  T2-1c — [WeakRvwmoLin.rule14_linearization]
        ▼
      c : cand, [srvwmo_consistent], same image, same rows
        │  T1 — [WeakAxRealize]/[srvwmo_realizable] + the language lift
        ▼
      a promise-free run of the event machine
        │  adequacy + φ — [WeakEvAdequacy]
        ▼
      SAFETY

    The last four arrows are exactly [WeakSrvwmoCapstone.xv6_srvwmo_safe];
    the first two are [WeakRvwmoLinInd.t2lin_supply].

    ** THE TWO RESIDUAL HYPOTHESES (quoted verbatim from
       [WeakRvwmoGlue2.t2lin_of_l2''], which is where they are stated):

      (R-1) [l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0)] —
            L2′ PROPER, the per-site classification of every segment of
            every R-cycle.  DISCHARGED BY: L2′ proper, site class by site
            class (S6 §3's inventory: aq / fenced / branched / data-fed /
            CS-covered / bad) from the emission's site records and the
            certified configuration.  This is the project's remaining
            CONTENT; it is a hypothesis here and an axiom nowhere.

      (R-2) [walk_supply boot d0 (img_z (wgimg σ0)) N N] — THE
            CERTIFICATION WALK: [WeakRvwmoCert4]'s [segs_run] run around
            the cycle from the realized hull, ending with the whole graph's
            writes in the log ([log_of]).  DISCHARGED BY: the walk itself
            ([WeakRvwmoCert3.cert_segment'] per segment plus the full-log
            fact); the debts inside it — (P-3) [wit_fence_ub] and (P-4)
            progress to the instruction boundary — are quantified over the
            candidates the walk builds and so cannot be hoisted above it
            (Glue2 §4 (iii)).

    Everything else is proved.  In particular the WP package (both
    flavours, φ and the F3″ registration seam) is the ONLY Iris-side
    obligation, and it is [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s premise
    (b) verbatim — no kernel premise, no robustness package, no retag.

    ** SCOPE: DEVICE-QUIET.  [gdexec_qconf] is the QUIESCENT conformance
    bundle — each hart's row is emitted at the CONSTANT fabric [λ _, d0]
    and its emission is [em_devfree].  So the theorem covers every graph of
    the xv6 image in which no hart performs an MMIO block.  The FULL
    BUNDLE — a MOVING fabric, dev blocks interleaved in a global device
    order — is [WeakRvwmoLin2.fconf_trace_realize], composed here as
    [xv6_rvwmo_safe_modulo_F] (§3), whose acyclicity premise is the
    REVISED axiom [gfexec_consistent'] taken as a hypothesis; see §3's
    TODO for what it would take to derive it from [l2_claim] the way §2
    does for the quiescent bundle.

    A LEAF: nothing imports this file.  Nothing below is [Admitted] or
    [Axiom]-ed. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvAdequacy.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakInterp.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakEvInst.
Require Import WeakGhost.
Require Import WeakEvAdequacy.
Require Import WeakEvCapstone.
Require Import WeakSrvwmoCapstone.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoLinInd.
Require Import WeakRvwmoFab.
Require Import WeakRvwmoLin2.
Require Import WeakRvwmoConfWit2.
Require Import WeakRvwmoGlue.
Require Import WeakRvwmoGlue2.

(* ====================================================================== *)
(** * 1. THE BOOT TIE, discharged at the canonical [boot]

    [boot] is read off the booted program-state list, so the boot equation
    the whole route carries ([boot <$> seq 0 N = eps_init σ0]) is not a
    hypothesis at the canonical choice — it is this list identity. *)

Lemma default_lookup_seq {A} (d : A) (l : list A) :
  (λ i, default d (l !! i)) <$> seq 0 (length l) = l.
Proof.
  apply list_eq. intros i. rewrite list_lookup_fmap.
  destruct (decide (i < length l)%nat) as [Hi|Hi].
  - rewrite lookup_seq_lt; [|exact Hi]. simpl.
    destruct (l !! i) as [a|] eqn:E; [done|].
    apply lookup_ge_None in E. lia.
  - rewrite lookup_seq_ge; [|lia]. simpl.
    symmetry. apply lookup_ge_None. lia.
Qed.

(** The canonical boot function and hart count of a booted state. *)
Definition xboot (σ0 : wgstate) : agent → pexv6 :=
  λ i, default (PDisk None) (eps_init σ0 !! i).
Definition xN (σ0 : wgstate) : nat := length (eps_init σ0).

Lemma xboot_seq (σ0 : wgstate) : xboot σ0 <$> seq 0 (xN σ0) = eps_init σ0.
Proof. apply (default_lookup_seq (PDisk None) (eps_init σ0)). Qed.

(* ====================================================================== *)
(** * 2. THE TIER-2 CAPSTONE, MODULO [l2_claim] AND [walk_supply] *)

(** ** 2.1 The workhorse, at an arbitrary boot tie.

    The premise list is [WeakRvwmoGlue2.t2lin_of_l2'']'s, verbatim, plus
    the two model-side clauses about the graph.  The conclusion is
    [WeakSrvwmoCapstone.xv6_srvwmo_safe]'s, with T2-LIN's own output —
    [RacyD]-acyclicity — exposed as the first conjunct and the realizing
    candidate existentially quantified (it is BUILT here; at tier 1 it was
    supplied). *)
Theorem xv6_rvwmo_safe_modulo_gen (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  (* (a) the fresh era, and the boot tie *)
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  (* (b) THE WP PACKAGE, in its two flavours *)
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) THE L2′ PER-SITE CLAIM *)
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  (* (R-2) THE CERTIFICATION WALK *)
  walk_supply boot d0 (img_z (wgimg σ0)) N N →
  (* (c) THE MODEL SIDE: a consistent, conformant graph of the xv6 image *)
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 (img_z (wgimg σ0)) N GD →
  (* T2-LIN *)
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (* T2-1c ∘ T1 ∘ the language lift: the graph IS realized *)
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (* ADEQUACY, candidate-independent *)
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hb1 Hb2 Hwp Hwpp Hl2 Hwalk GD Hcons Hq.
  destruct Hfr as (Hgen & Hpow & Hgen0 & Hlog & Hws).
  have Hfr : fresh_era gen σ0 by (rewrite /fresh_era; split_and!).
  (* the induction step, from the per-site claim *)
  have Hkill : cycle_kill boot d0 (img_z (wgimg σ0)) N.
  { by eapply (cycle_kill_of_l2'' Σ gen σ0 D Nm P boot d0 N). }
  (* T2-LIN itself *)
  have Hacy : ∀ x, ¬ tc (RacyD GD) x x.
  { by eapply (t2lin_of_l2'' Σ gen σ0 D Nm P boot d0 N). }
  (* topo ∘ T2-1c: the sRVWMO candidate *)
  destruct (t2lin_supply boot d0 (img_z (wgimg σ0)) N GD N Hkill Hcons Hq
              (gdexec_qconf_nharts _ _ _ _ _ Hq))
    as (c & pst & Hsr & Himg & Hpst0 & Hprog).
  have Himg' : cd_img c = img_z (wgimg σ0).
  { by rewrite Himg (gdexec_qconf_img _ _ _ _ _ Hq). }
  have Hpst0' : pst 0%nat = eps_init σ0 by rewrite Hpst0 Hb1.
  have Hdv0 : (λ _ : nat, d0) 0%nat = wgdev σ0 by exact Hb2.
  (* T1 ∘ adequacy *)
  destruct (xv6_srvwmo_safe Σ gen σ0 D c pst (λ _, d0) Hgen Hpow Hgen0 Hlog
              Hws Hwp Hsr Himg' Hpst0' Hdv0 Hprog)
    as (Hreal & Hvf & Hred).
  split_and!; [exact Hacy| |exact Hvf|exact Hred].
  destruct Hreal as (P' & σ' & Hr & Hlg & Hpg).
  by exists c, pst, P', σ'.
Qed.

(** ** 2.2 THE CAPSTONE, at the canonical boot tie.

    [boot], [N] and [d0] are read off σ0, so §1's list identity discharges
    the boot equation and only the two residual hypotheses remain. *)
Theorem xv6_rvwmo_safe_modulo (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  walk_supply (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) (xN σ0) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hwalk GD Hcons Hq.
  exact (xv6_rvwmo_safe_modulo_gen Σ gen σ0 D Nm P (xboot σ0) (wgdev σ0)
           (xN σ0) Hfr (xboot_seq σ0) eq_refl Hwp Hwpp Hl2 Hwalk
           GD Hcons Hq).
Qed.

(* ====================================================================== *)
(** * 3. THE FULL-BUNDLE VARIANT (a MOVING fabric)

    [WeakRvwmoLin2.fconf_trace_realize] delivers, from the REVISED axiom
    [gfexec_consistent'] (RVWMO⁻+deps consistency plus acyclicity of
    po ∪ rf ∪ gmo|W ∪ dev) and the fabric conformance bundle
    [gfexec_conf], a linearization that is simultaneously
    sRVWMO-consistent and fabric-ordered, with the moving device stream
    [λ k, fab (dcnt GF (cd_tr c) k)] and [dv 0 = d0].  Composing it with
    [xv6_srvwmo_safe] is then the same two lines as §2.

    *** TODO — WHAT IS NOT DONE HERE. ***  [gfexec_consistent'] is a
    HYPOTHESIS of this theorem, not derived from [l2_claim]: there is no
    Glue mirror for the fabric bundle.  Concretely, what is missing is

      (F-a) a fabric analogue of [WeakRvwmoGlue2.cycle_kill_of_l2''] —
            i.e. [WeakRvwmoFabInd.cycle_kill_F] discharged from a
            per-site claim stated over [gfexec_conf] rows.  [Glue]/[Glue2]
            are stated for the QUIESCENT bundle throughout (their
            [l2_claim], [cut_supply], [walk_supply], [cert_supply] all
            quantify over [gdexec_qconf]), so this is a restatement plus
            a re-proof, not a corollary.  [WeakRvwmoFabInd.cycle_kill_of_F]
            runs the OTHER way (the fabric kill subsumes the quiescent
            one at [gf_dev = []]), so it does not help here.
      (F-b) even given (F-a), [WeakRvwmoFabInd.t2lin_supply_F]'s output is
            guarded by [tr_dev_ordered] (FabInd §5: the T2-1c
            linearization does not visit dev blocks in [gf_dev]'s order),
            whereas [fconf_trace_realize] avoids the guard by building a
            fabric-ordered trace directly from [gfexec_consistent']'s
            EXTRA acyclicity clause.  So (F-a) would have to target
            [ptrace_relF] acyclicity, not [RacyF] acyclicity — a strictly
            stronger kill obligation than §2's.

    Until (F-a)/(F-b) land, the honest statement of the full bundle is the
    one below: the moving-fabric safety theorem, from the revised axiom. *)
Theorem xv6_rvwmo_safe_modulo_F (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (boot : agent → pexv6) (d0 : dev_state) (fab : nat → dev_state)
    (N : nat) (GF : gfexec) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  wp_package Σ gen σ0 D →
  (* the model side: the REVISED axiom and the fabric conformance bundle *)
  gfexec_consistent' GF →
  gfexec_conf boot d0 fab GF →
  gx_img (gd_g (gf_gd GF)) = img_z (wgimg σ0) →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  (∃ (c : cand) (pst : nat → list pexv6) (dv : nat → dev_state) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     dv 0%nat = wgdev σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hb1 Hb2 Hwp Hc' Hconf Himg HN.
  destruct Hfr as (Hgen & Hpow & Hgen0 & Hlog & Hws).
  destruct (fconf_trace_realize boot d0 fab GF N Hc' Hconf HN)
    as (L & pst & Hsr & Hcimg & _ & _ & Hp0 & Hd0 & Hok).
  set (c := cand_of (gd_g (gf_gd GF)) L) in *.
  set (dv := λ k, fab (dcnt GF (cd_tr c) k)).
  have Himg' : cd_img c = img_z (wgimg σ0) by rewrite Hcimg Himg.
  have Hpst0 : pst 0%nat = eps_init σ0 by rewrite Hp0 Hb1.
  have Hdv0 : dv 0%nat = wgdev σ0 by rewrite /dv Hd0 Hb2.
  destruct (xv6_srvwmo_safe Σ gen σ0 D c pst dv Hgen Hpow Hgen0 Hlog
              Hws Hwp Hsr Himg' Hpst0 Hdv0 Hok)
    as (Hreal & Hvf & Hred).
  split_and!; [|exact Hvf|exact Hred].
  destruct Hreal as (P' & σ' & Hr & Hlg & Hpg).
  by exists c, pst, dv, P', σ'.
Qed.

(* ====================================================================== *)
(** * 4. NON-VACUITY OF THE MODEL-SIDE PREMISES

    The theorem's (c) clause — a graph that is BOTH
    [rvwmo_minus_deps_consistent] AND [gdexec_qconf] — is satisfiable, at
    [WeakRvwmoConfWit2.mpwd] (MP: hart 0 stores the event flag, hart 1's
    real emitted [lw] reads that store), the first two-nonempty-row
    conformance bundle.

    THE HONEST LIMIT: [mpwd]'s image is [mp_img] — a synthetic 4-byte
    image — and its boot list [mp_boot] is a two-hart list, NOT
    [eps_init σ0] for any booted σ0 (which is one [PHart] per CPU plus the
    disk agent).  So only the GRAPH-SIDE premises are instantiated here;
    the [σ0]-facing clauses ([img_z (wgimg σ0)], [xboot σ0], [xN σ0]) are
    not, and cannot be at this witness.  A witness that ties both ends is
    exactly the two-event-row cycle witness the worklist prices as the
    next step (checkpoint item 1). *)
Theorem model_premises_nonvacuous
    (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    (d0 : dev_state) :
  rvwmo_minus_deps_consistent mpwd ∧
  gdexec_qconf (mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mp_img 2%nat mpwd.
Proof. split; [exact mpw_deps_consistent|apply mpw_qconf]. Qed.

(** The early-read variant of the same shape (the load sees the era image)
    — so the premise pair does not pin the rf edge either. *)
Theorem model_premises_nonvacuous'
    (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (ib0 ib1 : oib32)
    (d0 : dev_state) :
  rvwmo_minus_deps_consistent mpwd' ∧
  gdexec_qconf (mp_boot cpu0 cpu1 rs0 rs1 ib0 ib1) d0 mp_img 2%nat mpwd'.
Proof. split; [exact mpw'_deps_consistent|apply mpw'_qconf]. Qed.

(* ====================================================================== *)
(** * 5. THE AUDIT *)

Print Assumptions xv6_srvwmo_safe.
Print Assumptions xv6_rvwmo_safe_modulo_gen.
Print Assumptions xv6_rvwmo_safe_modulo.
Print Assumptions xv6_rvwmo_safe_modulo_F.
Print Assumptions model_premises_nonvacuous.
