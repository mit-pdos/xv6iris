(** * WeakEvLift.v — the per-event lifting rules, BATCHED (spike S4)

    Design: [claude-notes/design/weak-memory-event-granular.md] (the REVISED
    "expression-resident monad" section and the "reflective batching is
    MANDATORY" section); worklist
    [claude-notes/projects/weak-memory-event-lang.md] (deliverable S4).

    [WeakExec.wp_wrun_step] lifts ONE INSTRUCTION of [WeakLang]; this file
    lifts ONE EVENT of [WeakEvLang] — and then provides the BATCHED interface
    that is the actual leaf-facing one, because a per-node interface is not a
    viable proof shape at kernel-instruction size.

    ====================== HOW TO READ THIS FILE ======================

    §2 is the SEMANTICS: the core lifting rule for the cycle expression plus
    the arms with no memory content (boundary, [Ret], the parked fence).  §3 is
    the REFLECTION: a computable stepper [erun_silent] in the
    [DecodeSetU.goodbP] mold, with a ONCE-proven soundness lemma.  §4 is the
    PROOF INTERFACE: the n-step batched Iris rule that consumes §3 and advances
    a whole silent stretch in ONE application, with the register accounting done
    once for the stretch instead of once per node.  §5 is the two RAM events,
    which are where all the weak-memory content is.

    ================== THE STRUCTURAL FINDINGS (S4) ==================

    (F1) THE HART HAS NO SPURIOUS ARM.  With interrupt delivery placed where
         the design revision puts it (the PLIC thread's cross-thread wire
         write — [WeakEvLang] (D4)), a live [ECycle] has EXACTLY the successors
         its monad node licenses.  Every rule below is an ordinary
         deterministic-arm lifting; nothing has to be re-entrant and no rule
         needs a Löb.  (The pre-revision σ-resident draft had a hart-side
         delivery arm enabled at every state, which forced every rule either to
         absorb it by Löb or to expose it to its caller.  That cost is gone,
         and it is the clearest single win of the expression-resident design.)

    (F2) REDUCIBILITY IS THE ONE HONEST PARTIALITY.  A live [ECycle] at a stuck
         node ([GenericFail], a zero-width RAM write, an undecodable junk
         continuation, a declined MMIO width — [WeakEvLang] (D1)) has NO
         successor, so each rule SUPPLIES its arm's witness.  That is the
         event-granular replacement for the instruction-level totality
         argument, and it is per-node rather than per-instruction: no
         [sail_live], no [rv64d_live_residue], no completion premise.

    (F3) WHERE THE FROZEN LOG WAS LOAD-BEARING (the S4 question), and what
         replaced it:

         (a) [WeakRacy.wadm_down] / [wadm_filter_down] transport a read's
             ADMISSIBILITY from the state at which the read actually happens
             DOWN to the INSTRUCTION's pre-state, and their hypothesis is
             [wm_log s2 = wm_log s] — "the log did not move between the
             instruction's first event and its racy read".  That IS the
             frozen-log assumption, and as a statement about the machine it is
             false: another hart may append in between.  It was sound only
             because the instruction-atomic language ran the whole instruction
             in one step.  Here [ewp_ev_load] quantifies its continuation over
             the reads admissible AT THE READ EVENT'S OWN STATE, and no
             transport exists or is needed.  NOTHING replaces it: the
             assumption is deleted, not weakened.

         (b) [WeakInstr.wQ_load_w]'s [wm_log σ' = wm_log σ] ("a load
             instruction leaves the log alone") is false of a multi-event
             instruction.  The load EVENT does leave the log alone, and that is
             all any consumer ever used.

         (c) [WeakInstr.wwp_release_deposit] freezes the publisher's payload at
             [S (length (wm_log σ))] with [σ] the STORE INSTRUCTION's
             pre-state.  At event granularity the same lemma applies at the
             STORE EVENT's own state, where [ws_bounded (wgws σ c) (length
             (wglog σ))] is a conjunct of [WeakGhost.weak_state_interp].  A
             foreign append between the release fence and the store only makes
             the deposit's timestamp LARGER, and [ws_bounded] is re-established
             at every event — so the monotone invariant already carried this
             one and it was NOT load-bearing.

         (d) The only fact that genuinely needs a monotone restatement is one
             stated against an OLDER log, and the tree already has the
             discipline: [WeakGhost.wlog_lb] snapshots plus [wlog_lb_compare]
             (exactly how [WeakStarted]'s escrow is written).  Unchanged.

    (F4) THE INTERFERENCE-STABILITY TEST, and its verdict.  Every rule below is
         stated at an ARBITRARY [σ] satisfying [weak_state_interp] and
         re-establishes it at the successor; no rule mentions any state other
         than the event's own.  So "preserved by other threads' events" is not
         a side condition to check — it is the statement.  What the rules
         consume is (i) per-hart EXCLUSIVE resources ([hart_ws],
         [reg_pointsto_at]), which no foreign event can touch, and (ii) the
         C/D/S protocol fragments, which are exactly the interference-stable
         layer the tree already has ([nv_ok] survives a foreign append by
         [WeakGhost.nv_byte_app]; a foreign hart cannot write a byte whose
         latest-write element we own, because its own store rule would then be
         unprovable).  FAIL CRITERION 1 IS TESTED AND NOT HIT.

    (F5) FAIL CRITERION 2 (an invariant spanning several events of one
         instruction).  The audit: [WkStartedLoad.wwp_started_load] holds the
         [started] escrow open across the WHOLE instruction; at event
         granularity §5's rules give the caller a mask-changing callback around
         ONE event, which is strictly EASIER — the escrow is opened at the read
         event and closed at the read event.  The lock's acquire is likewise
         safe because the RMW stays FUSED ([WeakEvLang] (D3)).  NOT HIT. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop invariants ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakPromise.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import WeakLang.
Require Import WeakBridge.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto.
Require Import WeakEvLang.
Require Import WeakEvAdequacy.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 0. Two pure facts about the store fold

    "The only coherence floors a store moves are the ones inside its window."
    Needed to turn the caller's per-byte φ payment into the per-address
    obligation [WeakGhost.nv_hart_coh_step] asks for. *)

Lemma store_fold_map (rl : bool) (t : nat) (base : Z) (l : list nat) (ws : wstate) :
  foldl (fun w a0 => store_post w rl a0 t) ws
        (map (fun j : nat => base + Z.of_nat j) l)
  = foldl (fun w j => store_post w rl (base + Z.of_nat j) t) ws l.
Proof.
  revert ws. induction l as [|j l IH]; intros ws; [reflexivity|]. simpl. by rewrite IH.
Qed.

Lemma coh_store_fold_nat (rl : bool) (t : nat) (base : Z) (l : list nat)
    (ws : wstate) (a : Z) :
  (coh ws a <
   coh (foldl (fun w j => store_post w rl (base + Z.of_nat j) t) ws l) a)%nat ->
  exists j : nat, j ∈ l /\ a = base + Z.of_nat j.
Proof.
  revert ws. induction l as [|j l IH]; intros ws Hc; [simpl in Hc; lia|].
  simpl in Hc. destruct (decide (a = base + Z.of_nat j)) as [->|Hne].
  - exists j. split; [apply elem_of_cons; by left|reflexivity].
  - destruct (IH (store_post ws rl (base + Z.of_nat j) t)) as (j' & Hj' & ->).
    { rewrite (coh_store_post_ne ws rl (base + Z.of_nat j) t a Hne). exact Hc. }
    exists j'. split; [apply elem_of_cons; by right|reflexivity].
Qed.

Lemma coh_store_post_run_moved (ws : wstate) (rl : bool) (base : Z)
    (cnt t : nat) (a : Z) :
  (coh ws a < coh (store_post_run ws rl base cnt t) a)%nat ->
  exists j : nat, (j < cnt)%nat /\ a = base + Z.of_nat j.
Proof.
  rewrite /store_post_run /store_post_bytes store_fold_map. intros Hc.
  destruct (coh_store_fold_nat rl t base (seq 0 cnt) ws a Hc) as (j & Hj & ->).
  apply elem_of_seq in Hj. exists j. split; [lia|reflexivity].
Qed.

(* ====================================================================== *)
(** ** 1. Opening [weak_state_interp] at one hart

    σ is [wgstate] and the interpretation is [WeakGhost.weak_state_interp]
    VERBATIM, so "opening" is one focusing lemma per σ-update shape of
    [WeakEvLang] §2. *)

(** The [wstate] twin of [RiscvPtsto.gregs_interp_acc_at] — [WeakGhost]'s
    [wws_interp_acc] is stated at the AMBIENT [cpu_id] and every rule here
    names its hart explicitly. *)
Lemma wws_interp_acc_at `{!riscvGS Σ, !weakGS Σ} (c : CPU) (f : CPU -> wstate) :
  wws_interp f ⊢ wws_auth c (f c) ∗
    (∀ ws', wws_auth c ws' -∗ wws_interp (<[c := ws']> f)).
Proof.
  rewrite /wws_interp. iIntros "H".
  iDestruct (big_sepS_delete _ _ c with "H") as "[Hcur Hrest]";
    [apply elem_of_fin_to_set|].
  iFrame "Hcur". iIntros (ws') "Hws'".
  iApply (big_sepS_delete _ _ c); [apply elem_of_fin_to_set|].
  rewrite gws_insert_eq. iFrame "Hws'".
  iApply (big_sepS_mono with "Hrest").
  intros c0 Hc0. apply elem_of_difference in Hc0 as [_ Hne].
  rewrite gws_insert_ne; [done|].
  intros ->. apply Hne, elem_of_singleton. reflexivity.
Qed.

Lemma gregs_interp_ext `{!riscvGS Σ} (gr gr' : CPU -> regstate) :
  (forall c, gr c = gr' c) -> gregs_interp gr ⊣⊢ gregs_interp gr'.
Proof.
  intros Hext. rewrite /gregs_interp. apply big_sepS_proper.
  intros c _. by rewrite Hext.
Qed.

Section interp.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** A [RegRead] event writes the register file back UNCHANGED, and
      [ewg_reg σ c (wgregs σ c)] is pointwise — not syntactically — [σ]
      (this tree assumes no functional extensionality).  [gregs_interp] is a
      big-op over [CPU], hence determined pointwise. *)
  Lemma weak_state_interp_reg_id (σ : wgstate) (c : CPU) :
    weak_state_interp (ewg_reg σ c (wgregs σ c)) -∗ weak_state_interp σ.
  Proof.
    rewrite /weak_state_interp /ewg_reg.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    rewrite (gregs_interp_ext (<[c := wgregs σ c]> (wgregs σ)) (wgregs σ)).
    { by iIntros "H". }
    intros c0. destruct (decide (c0 = c)) as [->|Hne].
    - by rewrite greg_insert_eq.
    - by rewrite greg_insert_ne.
  Qed.

  Lemma weak_state_interp_pin (σ : wgstate) :
    weak_state_interp σ ⊢ ⌜wgpow σ = true /\ wggen σ = 0%nat⌝.
  Proof. rewrite /weak_state_interp. by iIntros "(%Hpin & _)". Qed.

  (** THE REGISTER CONJUNCT.  [ewg_reg] touches nothing else, so the closing
      wand is unconditional — this is the whole cost of a [RegWrite] event. *)
  Lemma weak_state_interp_regs (σ : wgstate) (c : CPU) :
    weak_state_interp σ ⊢ reg_interp_at (cpu_reg_name c) (wgregs σ c) ∗
      (∀ rs', reg_interp_at (cpu_reg_name c) rs' -∗
         weak_state_interp (ewg_reg σ c rs')).
  Proof.
    rewrite /weak_state_interp /ewg_reg.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    iIntros "(%Hpin & %Hbnd & %Hnv & %Hwf & Hgr & $)".
    iDestruct (gregs_interp_acc_at c with "Hgr") as "[$ Hcl]".
    iIntros (rs') "Hrs'". iDestruct ("Hcl" with "Hrs'") as "Hgr".
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    rewrite /insert /greg_insert. iExact "Hgr".
  Qed.

  (** THE MEMORY CONJUNCTS, in the shape every RAM event needs: the log
      authority, the latest-write map and this hart's view cell, with the three
      machine invariants handed out and taken back.  [ewg_store] is the general
      shape ([ewg_ws] is its [lg' = wglog σ] instance). *)
  Lemma weak_state_interp_mem (σ : wgstate) (c : CPU) :
    weak_state_interp σ ⊢
      ⌜forall c' : CPU, ws_bounded (wgws σ c') (length (wglog σ))⌝ ∗
      ⌜no_violation (wglog σ) (wgws σ)⌝ ∗ ⌜wlog_wf (wglog σ)⌝ ∗
      wlog_auth (wglog σ) ∗ wlat_interp (wgimg σ) (wglog σ) ∗
      wws_auth c (wgws σ c) ∗
      (∀ (ws' : wstate) (lg' : list wmsg),
         ⌜(length (wglog σ) ≤ length lg')%nat⌝ -∗
         ⌜ws_bounded ws' (length lg')⌝ -∗
         ⌜nv_hart lg' c ws'⌝ -∗
         ⌜exists ms, lg' = (wglog σ ++ ms)%list /\
                (forall m, m ∈ ms -> wm_tid m = Some (fin_to_nat c))⌝ -∗
         ⌜wlog_wf lg'⌝ -∗
         wlog_auth lg' -∗ wlat_interp (wgimg σ) lg' -∗ wws_auth c ws' -∗
         weak_state_interp (ewg_store σ c ws' lg')).
  Proof.
    rewrite /weak_state_interp /ewg_store.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    iIntros "(%Hpin & %Hbnd & %Hnv & %Hwf & $ & $ & Hlog & Hlat & Hws)".
    iDestruct (wws_interp_acc_at c with "Hws") as "[Hwsc Hwscl]".
    iFrame "Hlog Hlat Hwsc". iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iIntros (ws' lg') "%Hlen %Hb' %Hnvh %Hown %Hwf' Hlog Hlat Hwsc".
    iDestruct ("Hwscl" with "Hwsc") as "Hws".
    iSplitR; [by iPureIntro|].
    iSplitR.
    { iPureIntro. intros c0. destruct (decide (c0 = c)) as [->|Hne].
      - rewrite gws_insert_eq. exact Hb'.
      - rewrite gws_insert_ne; [|done].
        exact (ws_bounded_mono _ _ _ (Hbnd c0) Hlen). }
    iSplitR.
    { iPureIntro. destruct Hown as (ms & Hms & Hms2). rewrite Hms.
      apply (no_violation_step (wglog σ) ms (wgws σ) _ c Hnv Hbnd Hms2).
      - intros c0 Hne. by rewrite gws_insert_ne.
      - rewrite gws_insert_eq -Hms. exact Hnvh. }
    iSplitR; [by iPureIntro|]. iFrame "Hlog Hlat Hws".
  Qed.

End interp.

(* ====================================================================== *)
(** ** 2. The core lifting rule, and the arms with no memory content *)

Section core.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma ewp_ecycle (gen : nat) (c : CPU) (m : M unit)
      (fn : option (bool * bool * bool * bool)) :
    gen = 0%nat ->
    (∀ σ, weak_state_interp σ ={⊤,∅}=∗
       ⌜exists e' σ', ecycle_step gen σ c m fn e' σ'⌝ ∗
       ▷ (∀ e' σ', ⌜ecycle_step gen σ c m fn e' σ'⌝ ={∅,⊤}=∗
            weak_state_interp σ' ∗ EWP e' @ ⊤)) -∗
    EWP (ECycle gen c m fn) @ ⊤.
  Proof.
    iIntros (Hgen) "H".
    iApply (wp_lift_step (Λ := weak_ev_lang)); first done.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct (weak_state_interp_pin σ with "Hσ") as %[Hpow Hgen0].
    have Hlive : ethread_live σ gen
      by rewrite /ethread_live Hgen Hgen0; split.
    iMod ("H" $! σ with "Hσ") as "[%Hred Hk]".
    iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (e' & σ' & Hstep).
      exists [], e', σ', []. right; left. exists gen, c, m, fn.
      split_and!; try reflexivity. left. by split. }
    iIntros (e2 σ2 efs Hstep) "!>".
    apply eprim_step_cycle_inv in Hstep as (-> & -> & Harm).
    destruct Harm as [(_ & Hcy)|(Hnl & _)]; [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! e2 σ2 with "[//]") as "[$ $]". by iModIntro.
  Qed.

  (** THE BOUNDARY: [ELoop] fetches a fresh instruction.  σ does not move — the
      FETCH itself is an event of the cycle that follows, which is exactly the
      granularity claim. *)
  Lemma ewp_eloop (gen : nat) (c : CPU) :
    gen = 0%nat ->
    ▷ (∀ tick : bool, EWP (ECycle gen c (riscv_step tick) None) @ ⊤) -∗
    EWP (ELoop gen c) @ ⊤.
  Proof.
    iIntros (Hgen) "H".
    iApply (wp_lift_step (Λ := weak_ev_lang)); first done.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct (weak_state_interp_pin σ with "Hσ") as %[Hpow Hgen0].
    have Hlive : ethread_live σ gen
      by rewrite /ethread_live Hgen Hgen0; split.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hcl".
    iSplitR.
    { iPureIntro. exists [], (ECycle gen c (riscv_step false) None), σ, [].
      by apply eprim_step_loop_live. }
    iIntros (e2 σ2 efs Hstep) "!>".
    apply eprim_step_loop_inv in Hstep as (-> & -> & Harm).
    destruct Harm as [(_ & -> & (tick & ->))|(Hnl & _)];
      [|by destruct (Hnl Hlive)].
    iIntros "_". iMod "Hcl" as "_". iModIntro. iFrame "Hσ".
    iSplitL; [|done]. iApply "H".
  Qed.

  (** THE INSTRUCTION END: [Ret] pops back to the boundary token, at
      [fn = None] (the park/fire discipline is local to the cycle — (D5)). *)
  Lemma ewp_ev_ret (gen : nat) (c : CPU) (u : unit) :
    gen = 0%nat ->
    ▷ EWP (ELoop gen c) @ ⊤ -∗
    EWP (ECycle gen c (Interface.Ret u) None) @ ⊤.
  Proof.
    iIntros (Hgen) "H". iApply (ewp_ecycle gen c _ None Hgen).
    iIntros (σ) "Hσ". iApply fupd_mask_intro; [set_solver|]. iIntros "Hcl".
    iSplitR; [iPureIntro; by do 2 eexists|].
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. destruct Hcy as (-> & ->).
    iMod "Hcl" as "_". iModIntro. iFrame "Hσ". iExact "H".
  Qed.

  (** THE PARKED FENCE FIRING — the only arm enabled while [fn ≠ None] (D5). *)
  Lemma ewp_ev_fence_fire (gen : nat) (c : CPU) (m : M unit)
      (pr pw sr sw : bool) (ws : wstate) :
    gen = 0%nat ->
    hart_ws c ws -∗
    ▷ (hart_ws c (fence_post ws pr pw sr sw) -∗
         EWP (ECycle gen c m None) @ ⊤) -∗
    EWP (ECycle gen c m (Some (pr, pw, sr, sw))) @ ⊤.
  Proof.
    iIntros (Hgen) "Hws H".
    iApply (ewp_ecycle gen c m (Some (pr, pw, sr, sw)) Hgen).
    iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_mem σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hlog & Hlat & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR; [iPureIntro; by do 2 eexists|].
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. destruct Hcy as (-> & ->).
    iMod "Hmask" as "_".
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (fence_post (wgws σ c) pr pw sr sw) with "Hwsa Hws")
      as "[Hwsa Hws]".
    iModIntro. iSplitR "Hws H".
    - iDestruct ("Hcl" $! (fence_post (wgws σ c) pr pw sr sw) (wglog σ)
                   with "[%] [%] [%] [%] [%] Hlog Hlat Hwsa") as "Hσ".
      + reflexivity.
      + destruct (Hbnd c) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
        rewrite /ws_bounded /fence_post /=. split_and!; try (simpl; lia).
        * destruct sr; [|lia]. destruct pr, pw; simpl; lia.
        * destruct sw; [|lia]. destruct pr, pw; simpl; lia.
        * intros a. exact (H7 a).
        * intros a tv Ha. exact (H8 a tv Ha).
      + apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
          [exact (no_violation_hart _ _ c Hnv)|].
        intros a Hlt. exfalso. rewrite /fence_post /coh /= in Hlt. lia.
      + exists []. rewrite app_nil_r. split; [reflexivity|].
        intros mm Hmm. by apply elem_of_nil in Hmm.
      + exact Hwf.
      + rewrite /ewg_store /ewg_ws. iExact "Hσ".
    - by iApply "H".
  Qed.

End core.

(* ====================================================================== *)
(** ** 3. REFLECTION: the computable silent stepper

    In the [DecodeSetU.goodbP] / [decode_bridge_ms] mold: a COMPUTABLE function
    stepping through consecutive non-memory monad nodes, answering [RegRead]
    from the register file it threads and moving it at [RegWrite], with a
    ONCE-proven soundness lemma.  A concrete instance is that lemma applied to
    ONE computed equation; the induction lives inside [erun_silent_sound] and
    the per-site proof term is O(1) in the length of the stretch.

    TWO DELIBERATE RESTRICTIONS, both matching cuts the tree already makes:

      - [Choose] is EXCLUDED.  [WeakBridge.wstep_ok] and
        [WeakRacy.wstep_ok_racy] both set the [Choose] arm to [False] for the
        same reason: with [Choose] in, the successor is not determined by the
        pre-state and a REFLECTIVE (functional) stepper cannot exist.  The
        language keeps the arm; a leaf that needs it uses §2 directly.
      - Every register the stretch touches must lie in a declared footprint
        [D], because the hart owns the register authority only there.  This is
        exactly the "the certification lists the touched registers" accounting
        today's leaves already do. *)

Definition esil_node (D : gset register) (rs : regstate) (m : M unit)
    : option (regstate * M unit) :=
  match m with
  | Interface.Ret _ => None
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (regstate * M unit) with
       | Interface.RegRead r _ => fun k =>
           if decide (r ∈ D) then Some (rs, k (register_lookup r rs)) else None
       | Interface.RegWrite r _ v => fun k =>
           if decide (r ∈ D) then Some (register_set r v rs, k tt) else None
       | Interface.InstrAnnounce _   => fun k => Some (rs, k tt)
       | Interface.BranchAnnounce _ _=> fun k => Some (rs, k tt)
       | Interface.CacheOp _         => fun k => Some (rs, k tt)
       | Interface.TlbOp _           => fun k => Some (rs, k tt)
       | Interface.TakeException _   => fun k => Some (rs, k tt)
       | Interface.ReturnException _ => fun k => Some (rs, k tt)
       | Interface.TranslationStart _=> fun k => Some (rs, k tt)
       | Interface.TranslationEnd _  => fun k => Some (rs, k tt)
       | Interface.CycleCount        => fun k => Some (rs, k tt)
       | Interface.Message _         => fun k => Some (rs, k tt)
       | Interface.GetCycleCount     => fun k => Some (rs, k 0%Z)
       | _ => fun _ => None
       end) k
  end.

Fixpoint erun_silent (n : nat) (D : gset register) (rs : regstate) (m : M unit)
    : regstate * M unit :=
  match n with
  | 0%nat => (rs, m)
  | S n' =>
      match esil_node D rs m with
      | Some (rs', m') => erun_silent n' D rs' m'
      | None => (rs, m)
      end
  end.

(** The RELATIONAL silent step, at footprint [D]. *)
Definition esilD (D : gset register) (x y : M unit * regstate) : Prop :=
  esil_node D x.2 x.1 = Some (y.2, y.1).

Lemma erun_silent_sound (n : nat) (D : gset register) (rs : regstate)
    (m : M unit) (rs' : regstate) (m' : M unit) :
  erun_silent n D rs m = (rs', m') -> rtc (esilD D) (m, rs) (m', rs').
Proof.
  revert rs m. induction n as [|n IH]; intros rs m Heq.
  { simpl in Heq. by injection Heq as <- <-. }
  simpl in Heq. destruct (esil_node D rs m) as [[rs1 m1]|] eqn:Hnode.
  - apply (rtc_l (esilD D) (m, rs) (m1, rs1)); [exact Hnode|]. by apply IH.
  - by injection Heq as <- <-.
Qed.

(** THE SEMANTIC BRIDGE: a silent node IS an arm of [ecycle_step], and its
    successor is the only one there. *)
Lemma esil_node_ecycle (gen : nat) (σ : wgstate) (c : CPU) (D : gset register)
    (m m' : M unit) (rs' : regstate) :
  esil_node D (wgregs σ c) m = Some (rs', m') ->
  ecycle_step gen σ c m None (ECycle gen c m' None) (ewg_reg σ c rs')
  \/ (rs' = wgregs σ c /\
      ecycle_step gen σ c m None (ECycle gen c m' None) σ).
Proof.
  intros Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-;
    solve [ right; by split | left; by split ].
Qed.

Lemma esil_node_ecycle_inv (gen : nat) (σ : wgstate) (c : CPU)
    (D : gset register) (rs' : regstate) (m' m : M unit)
    (e' : eexpr) (σ' : wgstate) :
  esil_node D (wgregs σ c) m = Some (rs', m') ->
  ecycle_step gen σ c m None e' σ' ->
  e' = ECycle gen c m' None /\
  (σ' = ewg_reg σ c rs' \/ (rs' = wgregs σ c /\ σ' = σ)).
Proof.
  intros Hnode Hcy. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode, Hcy; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hcy as (-> & ->);
    (split; [reflexivity|]);
    solve [ right; by split | by left ].
Qed.

(* ====================================================================== *)
(** ** 4. THE PROOF INTERFACE: the n-step batched rule *)

Section batch.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Definition ereg_frame (c : CPU) (rs : regstate) (D : gset register) : iProp Σ :=
    ([∗ set] r ∈ D, reg_pointsto_at c r (DfracOwn 1) (register_lookup r rs))%I.

  Definition reg_agree_on (D : gset register) (rs rs' : regstate) : Prop :=
    forall r : register, r ∈ D -> register_lookup r rs = register_lookup r rs'.

  Lemma ereg_frame_ext c rs rs' D :
    reg_agree_on D rs rs' -> ereg_frame c rs D ⊣⊢ ereg_frame c rs' D.
  Proof.
    intros Hag. rewrite /ereg_frame. apply big_sepS_proper.
    intros r Hr. by rewrite (Hag r Hr).
  Qed.

  Lemma ereg_frame_agree c rs D (rs0 : regstate) :
    reg_interp_at (cpu_reg_name c) rs0 -∗ ereg_frame c rs D -∗
    ⌜reg_agree_on D rs rs0⌝.
  Proof.
    rewrite /ereg_frame. iIntros "Hi Hf".
    rewrite bi.pure_forall. iIntros (r). rewrite bi.pure_impl. iIntros (Hr).
    iDestruct (big_sepS_elem_of _ _ r Hr with "Hf") as "Hr".
    iDestruct (reg_valid_at c rs0 r (DfracOwn 1) (register_lookup r rs)
                 with "Hi Hr") as %Hv.
    iPureIntro. by symmetry.
  Qed.

  Lemma ereg_frame_update c rs D (r : register) (v : type_of_register r) rs0 :
    r ∈ D ->
    reg_interp_at (cpu_reg_name c) rs0 -∗ ereg_frame c rs D ==∗
    reg_interp_at (cpu_reg_name c) (register_set r v rs0) ∗
    ereg_frame c (register_set r v rs) D.
  Proof.
    intros HrD. rewrite /ereg_frame. iIntros "Hi Hf".
    iDestruct (big_sepS_delete _ _ r HrD with "Hf") as "[Hr Hrest]".
    iMod (reg_update_at c rs0 r (register_lookup r rs) v with "Hi Hr")
      as "[Hi Hr]".
    iModIntro. iFrame "Hi".
    iApply (big_sepS_delete _ _ r HrD).
    rewrite register_lookup_set. iFrame "Hr".
    iApply (big_sepS_mono with "Hrest").
    intros r' Hr'. apply elem_of_difference in Hr' as [_ Hne].
    assert (Hne' : r' <> r)
      by (intros ->; apply Hne, elem_of_singleton; reflexivity).
    by rewrite (irrelevant_register_set r' r rs v (register_beq_false r' r Hne')).
  Qed.

  (** THE TRANSPORT the batching needs, proved once: the stretch the caller
      COMPUTED at its own register file is the stretch the machine takes,
      because the only register values a silent node consults lie in [D] and
      the frame pins those. *)
  Lemma esil_node_agree D rs1 rs2 m m1 rs1' :
    reg_agree_on D rs1 rs2 -> esil_node D rs1 m = Some (rs1', m1) ->
    exists rs2', esil_node D rs2 m = Some (rs2', m1) /\ reg_agree_on D rs1' rs2'.
  Proof.
    intros Hag Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
    destruct oc; simpl in Hnode |- *; try discriminate Hnode;
      first
        [ (* RegRead: answered from the file, which agrees on [D] *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; rewrite (Hag _ HrD); exists rs2; by split
        | (* RegWrite: the same register moves on both sides *)
          case_decide as HrD; [|discriminate Hnode];
          injection Hnode as <- <-; eexists; (split; [done|]);
          intros r' Hr'; destruct (decide (r' = reg)) as [->|Hne];
          [ by rewrite !register_lookup_set
          | rewrite !(irrelevant_register_set r' reg _ regval
                        (register_beq_false r' reg Hne)); by apply Hag ]
        | injection Hnode as <- <-; exists rs2; by split ].
  Qed.

  (** ONE silent node.  Callers do not use this: they use [ewp_ev_batch]. *)
  Lemma ewp_ev_sil_node (gen : nat) (c : CPU) (D : gset register)
      (rs : regstate) (m m1 : M unit) (rs1 : regstate) :
    gen = 0%nat ->
    esil_node D rs m = Some (rs1, m1) ->
    ereg_frame c rs D -∗
    ▷ (ereg_frame c rs1 D -∗ EWP (ECycle gen c m1 None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hnode) "Hrf H". iApply (ewp_ecycle gen c m None Hgen).
    iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_regs σ c with "Hσ") as "[Hri Hcl]".
    iDestruct (ereg_frame_agree c rs D (wgregs σ c) with "Hri Hrf") as %Hag.
    destruct (esil_node_agree D rs (wgregs σ c) m m1 rs1 Hag Hnode)
      as (rs2 & Hnode2 & Hag2).
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro.
      destruct (esil_node_ecycle gen σ c D m m1 rs2 Hnode2) as [Hc|[_ Hc]];
        do 2 eexists; exact Hc. }
    iNext. iIntros (e' σ') "%Hcy". iMod "Hmask" as "_".
    destruct (esil_node_ecycle_inv gen σ c D rs2 m1 m e' σ' Hnode2 Hcy)
      as (-> & Hσ').
    iAssert (|==> reg_interp_at (cpu_reg_name c) rs2 ∗ ereg_frame c rs1 D)%I
      with "[Hri Hrf]" as ">[Hri Hrf]".
    { destruct m as [y|T oc k]; [by simpl in Hnode|].
      destruct oc; simpl in Hnode; try discriminate Hnode;
        first
          [ (* RegWrite: one register of the footprint moves *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iMod (ereg_frame_update c rs D _ regval (wgregs σ c) HrD
                    with "Hri Hrf") as "[Hri Hrf]";
            iModIntro; by iFrame "Hri Hrf"
          | (* RegRead: the file does not move *)
            case_decide as HrD; [|discriminate Hnode];
            injection Hnode as Hq1 Hq2; simpl in Hnode2;
            case_decide; [|discriminate Hnode2];
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (ereg_frame_ext c rs rs D)
          | injection Hnode as Hq1 Hq2; simpl in Hnode2;
            injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
            iModIntro; iFrame "Hri"; by iApply (ereg_frame_ext c rs rs D) ]. }
    iModIntro. destruct Hσ' as [->|[-> ->]].
    - iSplitL "Hri Hcl"; [by iApply "Hcl"|]. by iApply "H".
    - iSplitL "Hri Hcl".
      { iApply weak_state_interp_reg_id. by iApply "Hcl". }
      by iApply "H".
  Qed.

  (** THE BATCHED RULE.  The induction is HERE, not at the call site. *)
  Lemma ewp_ev_sil_rtc (gen : nat) (c : CPU) (D : gset register)
      (x y : M unit * regstate) :
    gen = 0%nat ->
    rtc (esilD D) x y ->
    ereg_frame c x.2 D -∗
    (ereg_frame c y.2 D -∗ EWP (ECycle gen c y.1 None) @ ⊤) -∗
    EWP (ECycle gen c x.1 None) @ ⊤.
  Proof.
    intros Hgen Hrtc. induction Hrtc as [x|x y0 z Hxy _ IH].
    - iIntros "Hrf H". by iApply "H".
    - destruct x as [m0 rs0], y0 as [m1 rs1]. simpl in Hxy |- *.
      iIntros "Hrf H".
      iApply (ewp_ev_sil_node gen c D rs0 m0 m1 rs1 Hgen Hxy with "Hrf").
      iNext. iIntros "Hrf". by iApply (IH with "Hrf").
  Qed.

  (** THE CALL-SITE FORM: ONE computed equation in, a whole stretch of [EWP]
      out.  This is the reflective interface the design's "reflective batching
      is MANDATORY" section asks for, and it is what a leaf uses. *)
  Lemma ewp_ev_batch (gen : nat) (c : CPU) (D : gset register) (n : nat)
      (m m' : M unit) (rs rs' : regstate) :
    gen = 0%nat ->
    erun_silent n D rs m = (rs', m') ->
    ereg_frame c rs D -∗
    (ereg_frame c rs' D -∗ EWP (ECycle gen c m' None) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    intros Hgen Hrun.
    exact (ewp_ev_sil_rtc gen c D (m, rs) (m', rs') Hgen
             (erun_silent_sound n D rs m rs' m' Hrun)).
  Qed.

End batch.

(* ====================================================================== *)
(** ** 5. The RAM events

    The two rules whose leaf content is weak-memory content.  Both are stated
    at the EVENT's own state — finding (F3) in force — and both give the caller
    a mask-changing callback AROUND THE SINGLE EVENT, so an escrow invariant is
    opened and closed at that one event (finding (F5)). *)

Section ram.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** *** 5a. THE RAM STORE — the C/D/S owned-store protocol step at ONE event.

      What the caller supplies, and nothing else:

        - the RETARGET, a ghost update taking the latest-write map at the
          EVENT's own log to the map at that log with this message appended.
          This is [WeakStore.wlat4_store_gen] / [wlat4_sync_store_gen]
          verbatim — the instruction-atomic store leaf's ghost content, now
          attached to a single event;
        - the φ PAYMENT, [nv_ok] at each byte the store touches, read off the
          caller's own C/D/S fragment ([WeakStore.nv_ok_wpt4] and friends).

      Note what is NOT required and cannot be: any statement about the log at
      any other state.  The message's timestamp is [S (length (wglog σ))] at
      the STORE EVENT's σ, and [ws_bounded] there is what makes
      [WeakInstr.wwp_release_deposit] apply (finding (F3)(c)). *)
  Lemma ewp_ev_store (gen : nat) (c : CPU) (n : N)
      (req : Interface.WriteReq.t n)
      (K : (option bool + Arch.abort)%type -> M unit) (ws : wstate) :
    gen = 0%nat ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    n <> 0%N ->
    acc_wf (Interface.WriteReq.pa req) n ->
    hart_ws c ws -∗
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
       ▷ |={∅,⊤}=>
         ⌜forall j : nat, (j < N.to_nat n)%nat ->
            nv_ok (wglog σ) c (acc_addr (Interface.WriteReq.pa req) j)⌝ ∗
         wlat_interp (wgimg σ)
           (wglog σ ++
            [wwrite_msg (Some (fin_to_nat c))
               (wm_class_of (classify (Interface.WriteReq.access_kind req)) ws)
               (Interface.WriteReq.pa req) n (Interface.WriteReq.value req)]) ∗
         (hart_ws c
            (store_post_run ws
               (ak_sync (classify (Interface.WriteReq.access_kind req)))
               (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
               (S (length (wglog σ)))) -∗
          EWP (ECycle gen c (K (inl None)) None) @ ⊤)) -∗
    EWP (ECycle gen c (Interface.Next (Interface.MemWrite n req) K) None) @ ⊤.
  Proof.
    iIntros (Hgen Hdev Hn Hacc) "Hws Hk".
    iApply (ewp_ecycle gen c _ None Hgen). iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_mem σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hlog & Hlat & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iDestruct (wlog_snapshot with "Hlog") as "[Hlog #Hlb]".
    iMod ("Hk" $! σ with "[//] [//] [%] Hlb Hlat") as "Hk"; [exact (Hbnd c)|].
    iModIntro. iSplitR.
    { iPureIntro. do 2 eexists. simpl. rewrite Hdev. by split_and!. }
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. rewrite Hdev in Hcy.
    destruct Hcy as (_ & -> & ->).
    iMod "Hk" as "(%Hnvok & Hlat & Hcont)".
    iMod (wlog_update (wglog σ) _ with "Hlog") as "Hlog".
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (store_post_run (wgws σ c)
               (ak_sync (classify (Interface.WriteReq.access_kind req)))
               (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
               (S (length (wglog σ)))) with "Hwsa Hws") as "[Hwsa Hws]".
    iModIntro. iSplitR "Hws Hcont"; [|by iApply "Hcont"].
    iApply ("Hcl" with "[%] [%] [%] [%] [%] Hlog Hlat Hwsa").
    - rewrite length_app /=. lia.
    - eapply store_post_run_bounded;
        [exact (Hbnd c)|rewrite length_app /=; lia|rewrite length_app /=; lia].
    - apply (nv_hart_coh_step _ c (wgws σ c)).
      + apply nv_hart_app_own; [exact (no_violation_hart _ _ c Hnv)|].
        intros mm Hmm. apply elem_of_list_singleton in Hmm as ->. reflexivity.
      + intros a Hlt. apply nv_byte_of_ok.
        destruct (coh_store_post_run_moved (wgws σ c)
                    (ak_sync (classify (Interface.WriteReq.access_kind req)))
                    (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
                    (S (length (wglog σ))) a Hlt) as (j & Hj & ->).
        intros n0. apply (nv_byte_app_own (wglog σ) _ c _ n0 (Hnvok j Hj n0)).
        intros mm Hmm. apply elem_of_list_singleton in Hmm as ->. reflexivity.
    - eexists. split; [reflexivity|]. intros mm Hmm.
      apply elem_of_list_singleton in Hmm as ->. reflexivity.
    - apply Forall_app. split; [exact Hwf|].
      apply Forall_singleton. by apply acc_wf_msg.
  Qed.

  (** *** 5b. THE RAM LOAD, RACY FORM — fail criterion 1's crux, restated at
      ONE event.

      The continuation is quantified over EVERY read the machine admits AT THE
      READ EVENT'S OWN STATE ([WeakPromise.read_ok] against that σ's log and
      this hart's view).  Compare [WeakRacy.wp_wracy_load], whose
      [WeakRacy.wadm] is stated at the INSTRUCTION's pre-state and reaches the
      read through [wadm_down]'s [wm_log s2 = wm_log s] — the frozen-log
      assumption of finding (F3)(a).  Here there is no earlier state to speak
      of, so there is nothing to transport and nothing to assume.

      [ak_latest = false] is what separates this arm from the FUSED RMW
      ([WeakEvLang] (D3)); a plain load (including a bare exclusive read) has
      it. *)
  Lemma ewp_ev_load (gen : nat) (c : CPU) (n : N)
      (req : Interface.ReadReq.t n)
      (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
      (ws : wstate) :
    gen = 0%nat ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = false ->
    hart_ws c ws -∗
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
       (* THE READ IS ENABLED: the caller exhibits one admissible read *)
       ⌜exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
          length tvs = N.to_nat n /\
          (forall j : nat, (j < N.to_nat n)%nat ->
             tvs.*2 !! j = Some (nth_byte w j)) /\
          read_ok (img_z (wgimg σ)) (wglog σ) ws
            (ak_sync (classify (Interface.ReadReq.access_kind req)))
            false (pa_z (Interface.ReadReq.pa req)) tvs⌝ ∗
       ▷ (∀ (w : bv (8 * n)) (tvs : list (nat * bv 8)),
            ⌜length tvs = N.to_nat n⌝ -∗
            ⌜forall j : nat, (j < N.to_nat n)%nat ->
               tvs.*2 !! j = Some (nth_byte w j)⌝ -∗
            ⌜read_ok (img_z (wgimg σ)) (wglog σ) ws
               (ak_sync (classify (Interface.ReadReq.access_kind req)))
               false (pa_z (Interface.ReadReq.pa req)) tvs⌝
            ={∅,⊤}=∗
              (* the φ payment: every floor this read moved is one the
                 caller's own C/D/S fragment covers *)
              ⌜forall a : Z,
                 (coh ws a <
                  coh (load_post_run ws
                         (ak_sync (classify (Interface.ReadReq.access_kind req)))
                         (pa_z (Interface.ReadReq.pa req)) tvs.*1) a)%nat ->
                 nv_ok (wglog σ) c a⌝ ∗
              wlat_interp (wgimg σ) (wglog σ) ∗
              (hart_ws c
                 (load_post_run ws
                    (ak_sync (classify (Interface.ReadReq.access_kind req)))
                    (pa_z (Interface.ReadReq.pa req)) tvs.*1) -∗
               EWP (ECycle gen c (K (inl (w, None))) None) @ ⊤))) -∗
    EWP (ECycle gen c (Interface.Next (Interface.MemRead n req) K) None) @ ⊤.
  Proof.
    iIntros (Hgen Hdev Hcoh Hlat) "Hws Hk".
    iApply (ewp_ecycle gen c _ None Hgen). iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_mem σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hlog & Hlat0 & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iDestruct (wlog_snapshot with "Hlog") as "[Hlog #Hlb]".
    iMod ("Hk" $! σ with "[//] [//] [%] Hlb Hlat0") as "[%Hen Hk]";
      [exact (Hbnd c)|].
    iModIntro. iSplitR.
    { iPureIntro. destruct Hen as (w & tvs & Hlen & Hbytes & Hrd).
      do 2 eexists. simpl. rewrite Hdev. split; [exact Hcoh|].
      left. split; [exact Hlat|]. exists w, tvs. by split_and!. }
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. rewrite Hdev in Hcy.
    destruct Hcy as (_ & [(_ & w & tvs & Hlen & Hbytes & Hrd & -> & ->)
                         |(Hbad & _)]); [|by rewrite Hlat in Hbad].
    iMod ("Hk" $! w tvs with "[//] [//] [//]") as "(%Hnvok & Hlat0 & Hcont)".
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (load_post_run (wgws σ c)
               (ak_sync (classify (Interface.ReadReq.access_kind req)))
               (pa_z (Interface.ReadReq.pa req)) tvs.*1) with "Hwsa Hws")
      as "[Hwsa Hws]".
    iModIntro. iSplitR "Hws Hcont"; [|by iApply "Hcont"].
    iDestruct ("Hcl" $! (load_post_run (wgws σ c)
                          (ak_sync (classify (Interface.ReadReq.access_kind req)))
                          (pa_z (Interface.ReadReq.pa req)) tvs.*1) (wglog σ)
                 with "[%] [%] [%] [%] [%] Hlog Hlat0 Hwsa") as "Hσ".
    - reflexivity.
    - apply load_post_run_bounded; [exact (Hbnd c)|].
      by eapply read_ok_ts_bounded.
    - apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
        [exact (no_violation_hart _ _ c Hnv)|].
      intros a Hlt. apply nv_byte_of_ok. exact (Hnvok a Hlt).
    - exists []. rewrite app_nil_r. split; [reflexivity|].
      intros mm Hmm. by apply elem_of_nil in Hmm.
    - exact Hwf.
    - rewrite /ewg_store /ewg_ws. iExact "Hσ".
  Qed.

End ram.

(* ====================================================================== *)
(** ** 6. THE FUSED RMW — the one-event lock acquire (S4 gap 2)

    [WeakEvLang] (D3): the exclusive read, the silent window and the
    conditional write are ONE event, so a lock acquire is ONE
    invariant/escrow access exactly as it is at instruction granularity —
    which is why fail criterion 2 does not bite at the acquire (finding
    (F5)).  The rule is [ewp_ev_store] and [ewp_ev_load] fused: its callback
    is opened once, around the single event, and it pays C/D/S for every
    floor the fused pair moved.

    THE ONE PLACE THE BATCHING FOOTPRINT LEAKS INTO A MEMORY-EVENT RULE, and
    the recorded reason.  The window's register writes happen INSIDE the
    event, so the successor's register file is the machine's [rs1] and the
    rule must move the register authority there in one ghost update — which
    it can only do for registers the caller's frame covers.  Hence the pure
    premise [Hconf]: every window the machine can take at this node is one
    the reflective stepper takes at the declared footprint [D].  It is a fact
    about the node (no state, no logic), it is exactly what the certification
    computes anyway, and without it the rule is not merely harder to prove —
    it is FALSE, because a window that writes an unowned register cannot
    re-establish [gregs_interp]. *)

Definition ermw_ok (σ : wgstate) (c : CPU) (n : N) (req : Interface.ReadReq.t n)
    (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
    (w : bv (8 * n)) (tvs : list (nat * bv 8)) (data : list (bv 8))
    (rl : bool) (m1 m2 : M unit) (rs1 : regstate) : Prop :=
  length tvs = N.to_nat n /\
  (forall j : nat, (j < N.to_nat n)%nat -> tvs.*2 !! j = Some (nth_byte w j)) /\
  read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c)
    (ak_sync (classify (Interface.ReadReq.access_kind req))) false
    (pa_z (Interface.ReadReq.pa req)) tvs /\
  excl_ok (wglog σ) (fin_to_nat c) (pa_z (Interface.ReadReq.pa req)) tvs
    (S (length (wglog σ))) /\
  data <> [] /\ length tvs = length data /\
  esilent_run (K (inl (w, None)), wgregs σ c) (m1, rs1) /\
  ewr_node m1 rl (pa_z (Interface.ReadReq.pa req)) data m2.

(** The successor's view: the load's post-state, then the store's. *)
Definition ermw_ws (σ : wgstate) (c : CPU) (n : N) (req : Interface.ReadReq.t n)
    (tvs : list (nat * bv 8)) (data : list (bv 8)) (rl : bool) : wstate :=
  store_post_run
    (load_post_run (wgws σ c)
       (ak_sync (classify (Interface.ReadReq.access_kind req)))
       (pa_z (Interface.ReadReq.pa req)) tvs.*1)
    rl (pa_z (Interface.ReadReq.pa req)) (length data) (S (length (wglog σ))).

Definition ermw_msg (σ : wgstate) (c : CPU) (n : N) (req : Interface.ReadReq.t n)
    (data : list (bv 8)) : wmsg :=
  WMsg (pa_z (Interface.ReadReq.pa req)) data (Some (fin_to_nat c)) WCexcl.

Section rmw.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** The combined accessor: [weak_state_interp_regs] and
      [weak_state_interp_mem] at ONCE, closing at [ewg_rmw] — which is the
      only σ-update shape that moves registers, views and the log together. *)
  Lemma weak_state_interp_rmw (σ : wgstate) (c : CPU) :
    weak_state_interp σ ⊢
      ⌜forall c' : CPU, ws_bounded (wgws σ c') (length (wglog σ))⌝ ∗
      ⌜no_violation (wglog σ) (wgws σ)⌝ ∗ ⌜wlog_wf (wglog σ)⌝ ∗
      reg_interp_at (cpu_reg_name c) (wgregs σ c) ∗
      wlog_auth (wglog σ) ∗ wlat_interp (wgimg σ) (wglog σ) ∗
      wws_auth c (wgws σ c) ∗
      (∀ (rs' : regstate) (ws' : wstate) (lg' : list wmsg),
         ⌜(length (wglog σ) ≤ length lg')%nat⌝ -∗
         ⌜ws_bounded ws' (length lg')⌝ -∗
         ⌜nv_hart lg' c ws'⌝ -∗
         ⌜exists ms, lg' = (wglog σ ++ ms)%list /\
                (forall m, m ∈ ms -> wm_tid m = Some (fin_to_nat c))⌝ -∗
         ⌜wlog_wf lg'⌝ -∗
         reg_interp_at (cpu_reg_name c) rs' -∗
         wlog_auth lg' -∗ wlat_interp (wgimg σ) lg' -∗ wws_auth c ws' -∗
         weak_state_interp (ewg_rmw σ c rs' ws' lg')).
  Proof.
    rewrite /weak_state_interp /ewg_rmw.
    cbn [wgregs wgimg wglog wgws wgdev wggen wgpow].
    iIntros "(%Hpin & %Hbnd & %Hnv & %Hwf & Hgr & $ & Hlog & Hlat & Hws)".
    iDestruct (gregs_interp_acc_at c with "Hgr") as "[$ Hgrcl]".
    iDestruct (wws_interp_acc_at c with "Hws") as "[Hwsc Hwscl]".
    iFrame "Hlog Hlat Hwsc". iSplitR; [by iPureIntro|].
    iSplitR; [by iPureIntro|]. iSplitR; [by iPureIntro|].
    iIntros (rs' ws' lg') "%Hlen %Hb' %Hnvh %Hown %Hwf' Hrs Hlog Hlat Hwsc".
    iDestruct ("Hgrcl" with "Hrs") as "Hgr".
    iDestruct ("Hwscl" with "Hwsc") as "Hws".
    iSplitR; [by iPureIntro|].
    iSplitR.
    { iPureIntro. intros c0. destruct (decide (c0 = c)) as [->|Hne].
      - rewrite gws_insert_eq. exact Hb'.
      - rewrite gws_insert_ne; [|done].
        exact (ws_bounded_mono _ _ _ (Hbnd c0) Hlen). }
    iSplitR.
    { iPureIntro. destruct Hown as (ms & Hms & Hms2). rewrite Hms.
      apply (no_violation_step (wglog σ) ms (wgws σ) _ c Hnv Hbnd Hms2).
      - intros c0 Hne. by rewrite gws_insert_ne.
      - rewrite gws_insert_eq -Hms. exact Hnvh. }
    iSplitR; [by iPureIntro|].
    rewrite /insert /greg_insert. iFrame "Hgr Hlog Hlat Hws".
  Qed.

  (** *** The register accounting of ONE silent node, factored out of
      [ewp_ev_sil_node] so that the fused RMW's window can reuse it at the
      GHOST level (there is no WP inside an event). *)
  Lemma ereg_frame_node (c : CPU) (D : gset register)
      (rs rs1 rs0 rs2 : regstate) (m m1 : M unit) :
    esil_node D rs m = Some (rs1, m1) ->
    esil_node D rs0 m = Some (rs2, m1) ->
    reg_interp_at (cpu_reg_name c) rs0 -∗ ereg_frame c rs D ==∗
    reg_interp_at (cpu_reg_name c) rs2 ∗ ereg_frame c rs1 D.
  Proof.
    intros Hnode Hnode2. iIntros "Hri Hrf".
    destruct m as [y|T oc k]; [by simpl in Hnode|].
    destruct oc; simpl in Hnode; try discriminate Hnode;
      first
        [ case_decide as HrD; [|discriminate Hnode];
          injection Hnode as Hq1 Hq2; simpl in Hnode2;
          case_decide; [|discriminate Hnode2];
          injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
          iMod (ereg_frame_update c rs D _ regval rs0 HrD with "Hri Hrf")
            as "[Hri Hrf]";
          iModIntro; by iFrame "Hri Hrf"
        | case_decide as HrD; [|discriminate Hnode];
          injection Hnode as Hq1 Hq2; simpl in Hnode2;
          case_decide; [|discriminate Hnode2];
          injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
          iModIntro; iFrame "Hri"; by iApply (ereg_frame_ext c rs rs D)
        | injection Hnode as Hq1 Hq2; simpl in Hnode2;
          injection Hnode2 as Hq3 Hq4; subst rs1 rs2;
          iModIntro; iFrame "Hri"; by iApply (ereg_frame_ext c rs rs D) ].
  Qed.

  Lemma ereg_frame_of c rs rs' D :
    reg_agree_on D rs rs' -> ereg_frame c rs D -∗ ereg_frame c rs' D.
  Proof.
    intros H. rewrite (ereg_frame_ext c rs rs' D H). iIntros "H". iExact "H".
  Qed.

  Lemma reg_agree_on_sym D rs rs' :
    reg_agree_on D rs rs' -> reg_agree_on D rs' rs.
  Proof. intros H r Hr. by rewrite (H r Hr). Qed.

  (** ... and a WHOLE silent stretch, at the ghost level: the authority
      follows the machine, the frame follows it pointwise on [D]. *)
  Lemma ereg_frame_rtc (c : CPU) (D : gset register) (x y : M unit * regstate) :
    rtc (esilD D) x y ->
    forall rs : regstate, reg_agree_on D rs x.2 ->
    reg_interp_at (cpu_reg_name c) x.2 -∗ ereg_frame c rs D ==∗
    reg_interp_at (cpu_reg_name c) y.2 ∗ ereg_frame c y.2 D.
  Proof.
    induction 1 as [x|x y0 z Hxy _ IH]; intros rs Hag.
    - iIntros "Hri Hrf". iModIntro. iFrame "Hri".
      by iApply (ereg_frame_of c rs x.2 D Hag).
    - iIntros "Hri Hrf". rewrite /esilD in Hxy.
      destruct (esil_node_agree D x.2 rs x.1 y0.1 y0.2
                  (reg_agree_on_sym D rs x.2 Hag) Hxy)
        as (rs2 & Hnode2 & Hag2).
      iMod (ereg_frame_node c D rs rs2 x.2 y0.2 x.1 y0.1 Hnode2 Hxy
              with "Hri Hrf") as "[Hri Hrf]".
      iApply (IH rs2 (reg_agree_on_sym D y0.2 rs2 Hag2) with "Hri Hrf").
  Qed.

  (** THE RULE.  Compare [WeakAcquire.wwp_acquire_swap]: same shape, one
      event instead of one instruction, and the escrow/invariant is opened
      around exactly this event. *)
  Lemma ewp_ev_rmw (gen : nat) (c : CPU) (n : N) (req : Interface.ReadReq.t n)
      (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
      (D : gset register) (rs : regstate) (ws : wstate) :
    gen = 0%nat ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = true ->
    acc_wf (Interface.ReadReq.pa req) n ->
    (* the window is footprint-confined — see the section header *)
    (forall (w : bv (8 * n)) (rs0 rs1 : regstate) (m1 : M unit),
       esilent_run (K (inl (w, None)), rs0) (m1, rs1) ->
       rtc (esilD D) (K (inl (w, None)), rs0) (m1, rs1)) ->
    hart_ws c ws -∗ ereg_frame c rs D -∗
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       ⌜reg_agree_on D rs (wgregs σ c)⌝ -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
       ⌜exists w tvs data rl m1 m2 rs1, ermw_ok σ c n req K w tvs data rl m1 m2 rs1⌝ ∗
       ▷ (∀ w tvs data rl m1 m2 rs1,
            ⌜ermw_ok σ c n req K w tvs data rl m1 m2 rs1⌝ ={∅,⊤}=∗
              ⌜forall a : Z,
                 (coh ws a < coh (ermw_ws σ c n req tvs data rl) a)%nat ->
                 nv_ok (wglog σ) c a⌝ ∗
              wlat_interp (wgimg σ) (wglog σ ++ [ermw_msg σ c n req data]) ∗
              (hart_ws c (ermw_ws σ c n req tvs data rl) -∗
               ereg_frame c rs1 D -∗
               EWP (ECycle gen c m2 None) @ ⊤))) -∗
    EWP (ECycle gen c (Interface.Next (Interface.MemRead n req) K) None) @ ⊤.
  Proof.
    iIntros (Hgen Hdev Hcoh Hlatest Hacc Hconf) "Hws Hrf Hk".
    iApply (ewp_ecycle gen c _ None Hgen). iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_rmw σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hri & Hlog & Hlat & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iDestruct (ereg_frame_agree c rs D (wgregs σ c) with "Hri Hrf") as %Hag.
    iMod ("Hk" $! σ with "[//] [//] [%] [//] Hlat") as "[%Hen Hk]";
      [exact (Hbnd c)|].
    iModIntro. iSplitR.
    { iPureIntro.
      destruct Hen as (w & tvs & data & rl & m1 & m2 & rs1 &
                       Hlen & Hbytes & Hrd & Hex & Hne & Hlend & Hwin & Hwr).
      do 2 eexists. simpl. rewrite Hdev. split; [exact Hcoh|]. right.
      split; [exact Hlatest|]. exists w, tvs, data, rl, m1, m2, rs1.
      by split_and!. }
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. rewrite Hdev in Hcy.
    destruct Hcy as (_ & [(Hbad & _)
                         |(_ & w & tvs & data & rl & m1 & m2 & rs1 &
                           Hlen & Hbytes & Hrd & Hex & Hne & Hlend & Hwin &
                           Hwr & -> & ->)]).
    { (* the PLAIN arm is excluded by its own guard — [WeakEvLang]'s finding
         F6: without it the fused RMW would not be atomic and this rule could
         not be stated. *)
      exfalso. by rewrite Hlatest in Hbad. }
    have Hok : ermw_ok σ c n req K w tvs data rl m1 m2 rs1 by split_and!.
    iMod ("Hk" $! w tvs data rl m1 m2 rs1 with "[//]")
      as "(%Hpay & Hlat & Hcont)".
    iMod (wlog_update (wglog σ) _ with "Hlog") as "Hlog".
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (ermw_ws σ c n req tvs data rl) with "Hwsa Hws") as "[Hwsa Hws]".
    iMod (ereg_frame_rtc c D (K (inl (w, None)), wgregs σ c) (m1, rs1)
            (Hconf w (wgregs σ c) rs1 m1 Hwin) rs Hag with "Hri Hrf")
      as "[Hri Hrf]".
    iModIntro. iSplitR "Hws Hrf Hcont"; [|by iApply ("Hcont" with "Hws Hrf")].
    iApply ("Hcl" with "[%] [%] [%] [%] [%] Hri Hlog Hlat Hwsa").
    - rewrite length_app /=. lia.
    - rewrite /ermw_ws. eapply store_post_run_bounded;
        [apply load_post_run_bounded;
           [exact (Hbnd c)|by eapply read_ok_ts_bounded]
        |rewrite length_app /=; lia|rewrite length_app /=; lia].
    - apply (nv_hart_coh_step _ c (wgws σ c)).
      + apply nv_hart_app_own; [exact (no_violation_hart _ _ c Hnv)|].
        intros mm Hmm. apply elem_of_list_singleton in Hmm as ->. reflexivity.
      + intros a Hlt. apply nv_byte_of_ok. intros n0.
        apply (nv_byte_app_own (wglog σ) _ c _ n0 (Hpay a Hlt n0)).
        intros mm Hmm. apply elem_of_list_singleton in Hmm as ->. reflexivity.
    - eexists. split; [reflexivity|]. intros mm Hmm.
      apply elem_of_list_singleton in Hmm as ->. reflexivity.
    - apply Forall_app. split; [exact Hwf|]. apply Forall_singleton.
      rewrite /wmsg_wf /ermw_msg /=. rewrite -Hlend Hlen.
      pose proof (pa_z_range (Interface.ReadReq.pa req)).
      rewrite /acc_wf in Hacc. lia.
  Qed.

End rmw.

(* ====================================================================== *)
(** ** 7. THE CERTIFICATION ADAPTER (batching item 3, S4 gap 3)

    The design's "certifications lift wholesale": today's leaf certification is
    an INTERPRETER RUN plus the instruction's memory effects
    ([WeakCert.wstep_cert cid pc (wP_eff tid es) …] with
    [es = [WEread akf pf nf; WEwrite akw ea 4 v]] — a fetch read and a data
    write).  At event granularity the same data is the pair "a REFLECTIVE
    silent stretch, then the memory node it stops at", and the adapter is one
    combinator per event kind: each consumes ONE computed equation
    ([erun_silent … = (rs', <the node>)], discharged by a single
    [vm_cast_no_check] at the call site — see [WeakEvStarted] §4) and one
    memory-event rule, and leaves an obligation ONLY at the memory event.

    A whole instruction is the combinators CHAINED, in the order the
    certification lists the effects; the register footprint [D] is threaded
    once and is never re-examined between events.  Cost per leaf: today's
    cost, plus one application per memory event — which is the design's stated
    target, and §4 of [WeakEvStarted] measures it. *)

Section adapter.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** *** 7a. The BARRIER event (the fence instruction's only memory event).

      No φ payment: a fence moves no coherence floor, only the view
      frontiers — which is [efence_apply_coh] and is why this rule has no
      [nv_ok] obligation at all. *)
  Lemma efence_apply_coh (ws : wstate) o (a : Z) :
    coh (efence_apply ws o) a = coh ws a.
  Proof. by destruct o as [[[[pr pw] sr] sw]|]. Qed.

  Lemma efence_apply_bounded (ws : wstate) (n : nat) o :
    ws_bounded ws n -> ws_bounded (efence_apply ws o) n.
  Proof.
    intros Hb. destruct o as [[[[pr pw] sr] sw]|]; [|exact Hb].
    destruct Hb as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    rewrite /ws_bounded /fence_post /=. split_and!; try (simpl; lia).
    - destruct sr; [|lia]. destruct pr, pw; simpl; lia.
    - destruct sw; [|lia]. destruct pr, pw; simpl; lia.
    - intros a. exact (H7 a).
    - intros a tv Ha. exact (H8 a tv Ha).
  Qed.

  Lemma ewp_ev_barrier (gen : nat) (c : CPU) (b : barrier_kind)
      (K : unit -> M unit) (ws : wstate) :
    gen = 0%nat ->
    hart_ws c ws -∗
    ▷ (hart_ws c (efence_apply ws (ebar_now b)) -∗
         EWP (ECycle gen c (K tt) (ebar_park b)) @ ⊤) -∗
    EWP (ECycle gen c (Interface.Next (Interface.Barrier b) K) None) @ ⊤.
  Proof.
    iIntros (Hgen) "Hws H". iApply (ewp_ecycle gen c _ None Hgen).
    iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_mem σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hlog & Hlat & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR; [iPureIntro; by do 2 eexists|].
    iNext. iIntros (e' σ') "%Hcy". simpl in Hcy. destruct Hcy as (-> & ->).
    iMod "Hmask" as "_".
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (efence_apply (wgws σ c) (ebar_now b)) with "Hwsa Hws")
      as "[Hwsa Hws]".
    iModIntro. iSplitR "Hws H"; [|by iApply "H"].
    iDestruct ("Hcl" $! (efence_apply (wgws σ c) (ebar_now b)) (wglog σ)
                 with "[%] [%] [%] [%] [%] Hlog Hlat Hwsa") as "Hσ".
    - reflexivity.
    - by apply efence_apply_bounded.
    - apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
        [exact (no_violation_hart _ _ c Hnv)|].
      intros a Hlt. exfalso. rewrite efence_apply_coh in Hlt. lia.
    - exists []. rewrite app_nil_r. split; [reflexivity|].
      intros mm Hmm. by apply elem_of_nil in Hmm.
    - exact Hwf.
    - rewrite /ewg_store /ewg_ws. iExact "Hσ".
  Qed.

  (** *** 7b. The four chaining combinators.

      Each is "ONE computed equation + ONE memory-event rule".  The stretch
      is advanced with [ewp_ev_batch] (n nodes, one application), the event
      with §5's rule, and the frame is handed on. *)

  Lemma ewp_ev_seq_ret (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (rs rs' : regstate) (m : M unit) (u : unit) :
    gen = 0%nat ->
    erun_silent nn D rs m = (rs', Interface.Ret u) ->
    ereg_frame c rs D -∗
    ▷ (ereg_frame c rs' D -∗ EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hrun) "Hrf H".
    iApply (ewp_ev_batch gen c D nn m (Interface.Ret u) rs rs' Hgen Hrun
              with "Hrf").
    iIntros "Hrf". iApply (ewp_ev_ret gen c u Hgen). by iApply "H".
  Qed.

  Lemma ewp_ev_seq_barrier (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (rs rs' : regstate) (m : M unit) (b : barrier_kind) (K : unit -> M unit)
      (ws : wstate) :
    gen = 0%nat ->
    erun_silent nn D rs m = (rs', Interface.Next (Interface.Barrier b) K) ->
    hart_ws c ws -∗ ereg_frame c rs D -∗
    ▷ (hart_ws c (efence_apply ws (ebar_now b)) -∗ ereg_frame c rs' D -∗
         EWP (ECycle gen c (K tt) (ebar_park b)) @ ⊤) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hrun) "Hws Hrf H".
    iApply (ewp_ev_batch gen c D nn m _ rs rs' Hgen Hrun with "Hrf").
    iIntros "Hrf". iApply (ewp_ev_barrier gen c b K ws Hgen with "Hws").
    iNext. iIntros "Hws". by iApply ("H" with "Hws Hrf").
  Qed.

  Lemma ewp_ev_seq_store (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (rs rs' : regstate) (m : M unit) (n : N) (req : Interface.WriteReq.t n)
      (K : (option bool + Arch.abort)%type -> M unit) (ws : wstate) :
    gen = 0%nat ->
    erun_silent nn D rs m = (rs', Interface.Next (Interface.MemWrite n req) K) ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    n <> 0%N ->
    acc_wf (Interface.WriteReq.pa req) n ->
    hart_ws c ws -∗ ereg_frame c rs D -∗
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
       ▷ |={∅,⊤}=>
         ⌜forall j : nat, (j < N.to_nat n)%nat ->
            nv_ok (wglog σ) c (acc_addr (Interface.WriteReq.pa req) j)⌝ ∗
         wlat_interp (wgimg σ)
           (wglog σ ++
            [wwrite_msg (Some (fin_to_nat c))
               (wm_class_of (classify (Interface.WriteReq.access_kind req)) ws)
               (Interface.WriteReq.pa req) n (Interface.WriteReq.value req)]) ∗
         (hart_ws c
            (store_post_run ws
               (ak_sync (classify (Interface.WriteReq.access_kind req)))
               (pa_z (Interface.WriteReq.pa req)) (N.to_nat n)
               (S (length (wglog σ)))) -∗
          ereg_frame c rs' D -∗
          EWP (ECycle gen c (K (inl None)) None) @ ⊤)) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hrun Hdev Hn Hacc) "Hws Hrf Hk".
    iApply (ewp_ev_batch gen c D nn m _ rs rs' Hgen Hrun with "Hrf").
    iIntros "Hrf".
    iApply (ewp_ev_store gen c n req K ws Hgen Hdev Hn Hacc with "Hws").
    iIntros (σ) "%Hws %Hwf %Hbnd #Hlb Hlat".
    iMod ("Hk" $! σ with "[//] [//] [//] Hlb Hlat") as "Hk". iModIntro. iNext.
    iMod "Hk" as "(%Hpay & Hlat & Hcont)". iModIntro. iFrame "Hlat".
    iSplitR; [by iPureIntro|]. iIntros "Hws". by iApply ("Hcont" with "Hws Hrf").
  Qed.

  Lemma ewp_ev_seq_load (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (rs rs' : regstate) (m : M unit) (n : N) (req : Interface.ReadReq.t n)
      (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
      (ws : wstate) :
    gen = 0%nat ->
    erun_silent nn D rs m = (rs', Interface.Next (Interface.MemRead n req) K) ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = false ->
    hart_ws c ws -∗ ereg_frame c rs D -∗
    (∀ σ : wgstate,
       ⌜wgws σ c = ws⌝ -∗ ⌜wlog_wf (wglog σ)⌝ -∗
       ⌜ws_bounded ws (length (wglog σ))⌝ -∗
       wlog_lb (wglog σ) -∗
       wlat_interp (wgimg σ) (wglog σ) ={⊤,∅}=∗
       ⌜exists (w : bv (8 * n)) (tvs : list (nat * bv 8)),
          length tvs = N.to_nat n /\
          (forall j : nat, (j < N.to_nat n)%nat ->
             tvs.*2 !! j = Some (nth_byte w j)) /\
          read_ok (img_z (wgimg σ)) (wglog σ) ws
            (ak_sync (classify (Interface.ReadReq.access_kind req)))
            false (pa_z (Interface.ReadReq.pa req)) tvs⌝ ∗
       ▷ (∀ (w : bv (8 * n)) (tvs : list (nat * bv 8)),
            ⌜length tvs = N.to_nat n⌝ -∗
            ⌜forall j : nat, (j < N.to_nat n)%nat ->
               tvs.*2 !! j = Some (nth_byte w j)⌝ -∗
            ⌜read_ok (img_z (wgimg σ)) (wglog σ) ws
               (ak_sync (classify (Interface.ReadReq.access_kind req)))
               false (pa_z (Interface.ReadReq.pa req)) tvs⌝
            ={∅,⊤}=∗
              ⌜forall a : Z,
                 (coh ws a <
                  coh (load_post_run ws
                         (ak_sync (classify (Interface.ReadReq.access_kind req)))
                         (pa_z (Interface.ReadReq.pa req)) tvs.*1) a)%nat ->
                 nv_ok (wglog σ) c a⌝ ∗
              wlat_interp (wgimg σ) (wglog σ) ∗
              (hart_ws c
                 (load_post_run ws
                    (ak_sync (classify (Interface.ReadReq.access_kind req)))
                    (pa_z (Interface.ReadReq.pa req)) tvs.*1) -∗
               ereg_frame c rs' D -∗
               EWP (ECycle gen c (K (inl (w, None))) None) @ ⊤))) -∗
    EWP (ECycle gen c m None) @ ⊤.
  Proof.
    iIntros (Hgen Hrun Hdev Hcoh Hlat) "Hws Hrf Hk".
    iApply (ewp_ev_batch gen c D nn m _ rs rs' Hgen Hrun with "Hrf").
    iIntros "Hrf".
    iApply (ewp_ev_load gen c n req K ws Hgen Hdev Hcoh Hlat with "Hws").
    iIntros (σ) "%Hws %Hwf %Hbnd #Hlb Hlat0".
    iMod ("Hk" $! σ with "[//] [//] [//] Hlb Hlat0") as "[%Hen Hk]".
    iModIntro. iSplitR; [by iPureIntro|]. iNext.
    iIntros (w tvs) "%H1 %H2 %H3".
    iMod ("Hk" $! w tvs with "[//] [//] [//]") as "(%Hpay & Hlat0 & Hcont)".
    iModIntro. iFrame "Hlat0". iSplitR; [by iPureIntro|].
    iIntros "Hws". by iApply ("Hcont" with "Hws Hrf").
  Qed.

End adapter.
