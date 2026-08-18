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

(** ... and the LOAD twin, which the fetch rule (§5c) needs: a load only moves
    the coherence floors of the bytes it read. *)

Lemma coh_load_post_at_ne (ws : wstate) (aq : bool) (vpre : nat) (a' : Z)
    (t : nat) (a : Z) :
  a <> a' -> coh (load_post_at ws aq vpre a' t) a = coh ws a.
Proof. intros Hne. rewrite /load_post_at /coh /= lookup_insert_ne //. Qed.

Lemma coh_load_fold_moved (aq : bool) (vpre : nat) (ats : list (Z * nat))
    (ws : wstate) (a : Z) :
  (coh ws a <
   coh (foldl (fun w at_ => load_post_at w aq vpre at_.1 at_.2) ws ats) a)%nat ->
  exists p, p ∈ ats /\ a = p.1.
Proof.
  revert ws. induction ats as [|p ats IH]; intros ws Hc; [simpl in Hc; lia|].
  simpl in Hc. destruct (decide (a = p.1)) as [->|Hne].
  - exists p. split; [apply elem_of_list_here|reflexivity].
  - destruct (IH (load_post_at ws aq vpre p.1 p.2)) as (p' & Hp' & Heq).
    { rewrite (coh_load_post_at_ne ws aq vpre p.1 p.2 a Hne). exact Hc. }
    exists p'. split; [by apply elem_of_list_further|exact Heq].
Qed.

Lemma coh_load_post_run_moved (ws : wstate) (aq : bool) (base : Z)
    (ts : list nat) (a : Z) :
  (coh ws a < coh (load_post_run ws aq base ts) a)%nat ->
  exists j : nat, (j < length ts)%nat /\ a = base + Z.of_nat j.
Proof.
  rewrite /load_post_run /load_post_bytes. intros Hc.
  destruct (coh_load_fold_moved aq (load_vpre ws aq) _ ws a Hc)
    as (p & Hp & Heq).
  apply elem_of_zip_with in Hp as (j & t & -> & Hj & _).
  apply elem_of_seq in Hj. simpl in Heq. exists j. split; [lia|exact Heq].
Qed.

(** ... and the [w_relp] flag a load leaves alone (the publisher's release
    arming survives its own fetch).  [WeakInstr.load_post_run_relp] says this
    too, but the event tier does not depend on that file. *)

Lemma load_post_fold_relp_ev (aq : bool) (vpre : nat) (ats : list (Z * nat)) :
  forall ws : wstate,
    w_relp (foldl (fun w at_ => load_post_at w aq vpre at_.1 at_.2) ws ats)
    = w_relp ws.
Proof. induction ats as [|a l IH]; [done|]. intros ws. simpl. by rewrite IH. Qed.

Lemma load_post_run_relp_ev (ws : wstate) (aq : bool) (base : Z) (ts : list nat) :
  w_relp (load_post_run ws aq base ts) = w_relp ws.
Proof. apply load_post_fold_relp_ev. Qed.

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

  (** D3, THE INVISIBILITY LEMMA.  [WeakGhost.weak_state_interp] mentions
      [wgregs]/[wgimg]/[wglog]/[wgws]/[wgdev]/[wggen]/[wgpow] and NOTHING
      ELSE, so a σ-step that moves only the announced instruction bits is
      invisible to it — BY CONVERSION, not by a proof.  This is what lets
      the [InstrAnnounce] node and the instruction boundary stay silent for
      every WP rule, and it is the reason the D3 acceptance test passes for
      the reflective silent stepper. *)
  Lemma weak_state_interp_ib (σ : wgstate) (c : CPU) (v : oib32) :
    weak_state_interp (ewg_ib σ c v) = weak_state_interp σ.
  Proof. reflexivity. Qed.

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
      exists [], e', σ', []. left. exists gen, c, m, fn.
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
    { iPureIntro. exists [], (ECycle gen c (riscv_step false) None),
        (ewg_ib σ c None), [].
      by apply eprim_step_loop_live. }
    iIntros (e2 σ2 efs Hstep) "!>".
    apply eprim_step_loop_inv in Hstep as (-> & -> & Harm).
    destruct Harm as [(_ & -> & (tick & ->))|(Hnl & _)];
      [|by destruct (Hnl Hlive)].
    iIntros "_". iMod "Hcl" as "_". iModIntro.
    (* D3: the RESTART clears [wgib], which the state interpretation cannot
       see ([weak_state_interp_ib] — a CONVERSION, so [iFrame] closes it
       with no rewriting at all).  That is the whole point of putting the
       announced bits in σ and not in a ghost. *)
    iFrame "Hσ".
    iSplitL; [|done]. iApply "H".
  Qed.

  (** THE INSTRUCTION END, AFTER THE G5 CONSTRUCTOR MERGE.  [Ret u] at
      [fn = None] IS the boundary value ([ELoop gen c] is a DEFINITION for
      it — [u] is [tt] because the monad's result type is [unit]), so this
      rule no longer costs a step: the old "pop to [ELoop]" transition and
      the old boundary rule are ONE rule now, and it is [ewp_eloop] above
      (the RESTART).  What survives here is the conversion, kept under its
      old name so that the certification adapter's statements do not move.
      THE ▷ IS GONE, deliberately: there is no step left to strip. *)
  Lemma ewp_ev_ret (gen : nat) (c : CPU) (u : unit) :
    gen = 0%nat ->
    EWP (ELoop gen c) @ ⊤ -∗
    EWP (ECycle gen c (Interface.Ret u) None) @ ⊤.
  Proof. iIntros (Hgen) "H". by destruct u. Qed.

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
      + destruct (Hbnd c) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
        rewrite /ws_bounded /fence_post /=. split_and!; try (simpl; lia).
        * destruct sr; [|lia]. destruct pr, pw; simpl; lia.
        * destruct sw; [|lia]. destruct pr, pw; simpl; lia.
        * intros a. exact (H7 a).
        * intros a tv Ha. exact (H8 a tv Ha).
        * intros r. exact (H9 r).
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

(** D3: THE σ-EFFECT OF A SILENT NODE, as a named three-way disjunction.

    Before D3 it was two-way — the node either wrote the register file or
    moved nothing.  The [InstrAnnounce] node now writes the hart's ANNOUNCED
    INSTRUCTION BITS ([WeakEvLang.ewg_ib]); that is a third shape, and it is
    the ONLY thing D3 adds here.  It costs the WP tier NOTHING, because
    [weak_state_interp_ib] is a conversion: no rule below changes its
    statement, no leaf sees it, and the reflective cursor keeps treating the
    announce as silent (so no [vm_cast] node count moves). *)
Definition esil_sigma (σ : wgstate) (c : CPU) (rs' : regstate) (σ' : wgstate)
    : Prop :=
  σ' = ewg_reg σ c rs'
  \/ (rs' = wgregs σ c /\ exists v : oib32, σ' = ewg_ib σ c v)
  \/ (rs' = wgregs σ c /\ σ' = σ).

(** THE SEMANTIC BRIDGE: a silent node IS an arm of [ecycle_step], and its
    successor is the only one there. *)
Lemma esil_node_ecycle (gen : nat) (σ : wgstate) (c : CPU) (D : gset register)
    (m m' : M unit) (rs' : regstate) :
  esil_node D (wgregs σ c) m = Some (rs', m') ->
  exists σ' : wgstate,
    ecycle_step gen σ c m None (ECycle gen c m' None) σ' /\
    esil_sigma σ c rs' σ'.
Proof.
  intros Hnode. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode |- *; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-;
    solve [ eexists; (split; [by split|]);
              right; left; (split; [reflexivity|by eexists])
          | eexists; (split; [by split|]); right; right; by split
          | eexists; (split; [by split|]); left; reflexivity ].
Qed.

Lemma esil_node_ecycle_inv (gen : nat) (σ : wgstate) (c : CPU)
    (D : gset register) (rs' : regstate) (m' m : M unit)
    (e' : eexpr) (σ' : wgstate) :
  esil_node D (wgregs σ c) m = Some (rs', m') ->
  ecycle_step gen σ c m None e' σ' ->
  e' = ECycle gen c m' None /\ esil_sigma σ c rs' σ'.
Proof.
  intros Hnode Hcy. destruct m as [y|T oc k]; [by simpl in Hnode|].
  destruct oc; simpl in Hnode, Hcy; try discriminate Hnode;
    try (case_decide; [|discriminate Hnode]);
    injection Hnode as <- <-; destruct Hcy as (-> & ->);
    (split; [reflexivity|]);
    solve [ right; left; (split; [reflexivity|by eexists])
          | right; right; by split | by left ].
Qed.

(* ====================================================================== *)
(** ** 3b. THE REFLECTIVE INTERFACE: TOTAL PROJECTIONS AND UNEVALUATED
           COMPOSITIONS (the finding-F8 form)

    THE RULE THIS SECTION EXISTS TO ENFORCE: **no call site ever writes a
    residual monad down.**  The spike's first form of §4's batched rule took
    the equation [erun_silent n D rs m = (rs', m')], and closing it at a real
    kernel instruction means NAMING [m'] — a Sail continuation whose readback
    normalises the whole rest of the instruction symbolically (MEASURED: did
    not finish in 110 s, against 0.1 s for the same run projected to a
    number).  The same is true of [rs']: the post-boot register file computes
    in 0.09 s and reads back in over three minutes.

    So the interface is restated over:

      - a CURSOR [ecur = regstate * M unit] and TOTAL functions on it
        ([esil], [ecur_read], [ecur_write], [ecur_bar]).  A certification is a
        CHAIN OF APPLICATIONS — [esil n2 D (ecur_read v (esil n1 D x))] — which
        is never normalised, and whose components are never named;
      - TOTAL PROJECTIONS with SMALL outputs ([enode_tag] : a number,
        [eread_req_at]/[ewrite_req_at] : the request record, [ebar_at] : the
        barrier kind).  Each per-site fact is one [vm_cast_no_check] whose
        right-hand side the caller writes by hand;
      - ONCE-PROVEN INVERSION LEMMAS ([eread_req_at_inv] & co.) by which the
        rules match on the residual's head.  The rules below consume the
        projection, not a syntactic pattern, so the residual and the register
        file stay unevaluated compositions from the first stretch to [Ret].

    Nothing here changes any rule's CONTENT: the same events, the same escrow
    accesses, the same φ payments. *)

(** THE CURSOR: the machine's register file and its residual monad. *)
Definition ecur : Type := (regstate * M unit)%type.

(** ONE SILENT STRETCH, as a total function of cursors. *)
Definition esil (n : nat) (D : gset register) (x : ecur) : ecur :=
  erun_silent n D x.1 x.2.

(** The three TOTAL RESUME functions — "the certification's answer at this
    event".  A read is answered by the VALUE READ, passed as a [Z] (the
    width lives in the node, so a [bv]-typed argument would make the cursor
    chain dependently typed for no gain: [Z_to_bv_bv_unsigned] converts). *)
Definition eread_resume (v : Z) (m : M unit) : M unit :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> M unit with
       | Interface.MemRead n _ => fun k => k (inl (Z_to_bv (8 * n) v, None))
       | _ => fun _ => m
       end) k
  | _ => m
  end.

Definition ewrite_resume (m : M unit) : M unit :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> M unit with
       | Interface.MemWrite _ _ => fun k => k (inl None)
       | _ => fun _ => m
       end) k
  | _ => m
  end.

Definition ebar_resume (m : M unit) : M unit :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M unit) -> M unit with
       | Interface.Barrier _ => fun k => k tt
       | _ => fun _ => m
       end) k
  | _ => m
  end.

(** CROSSING AN INSTRUCTION BOUNDARY: the next instruction starts at the
    previous one's final register file, with the fresh monad the boundary
    token hands out.  (This is what makes a MULTI-INSTRUCTION certification a
    composition too — [WeakEvStarted] §4.) *)
Definition ecur_loop (tick : bool) (x : ecur) : ecur := (x.1, riscv_step tick).

Definition ecur_read (v : Z) (x : ecur) : ecur := (x.1, eread_resume v x.2).
Definition ecur_write (x : ecur) : ecur := (x.1, ewrite_resume x.2).
Definition ecur_bar (x : ecur) : ecur := (x.1, ebar_resume x.2).

(** THE PROJECTIONS.  Every output is a value a caller can write by hand. *)
Definition enode_tag (m : M unit) : nat :=
  match m with
  | Interface.Ret _ => 0
  | Interface.Next oc _ =>
      match oc with
      | Interface.MemRead _ _ => 1
      | Interface.MemWrite _ _ => 2
      | Interface.Barrier _ => 3
      | Interface.Choose _ => 4
      | _ => 5
      end
  end.

Definition eread_req_at (n : N) (m : M unit) : option (Interface.ReadReq.t n) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (Interface.ReadReq.t n) with
       | Interface.MemRead n' req => fun _ =>
           match decide (n' = n) with
           | left Heq => Some (eq_rect n' Interface.ReadReq.t req n Heq)
           | right _ => None
           end
       | _ => fun _ => None
       end) k
  | _ => None
  end.

Definition ewrite_req_at (n : N) (m : M unit)
    : option (Interface.WriteReq.t n) :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option (Interface.WriteReq.t n) with
       | Interface.MemWrite n' req => fun _ =>
           match decide (n' = n) with
           | left Heq => Some (eq_rect n' Interface.WriteReq.t req n Heq)
           | right _ => None
           end
       | _ => fun _ => None
       end) k
  | _ => None
  end.

Definition ebar_at (m : M unit) : option barrier_kind :=
  match m with
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T
             return (T -> M unit) -> option barrier_kind with
       | Interface.Barrier b => fun _ => Some b
       | _ => fun _ => None
       end) k
  | _ => None
  end.

(** THE FOUR INVERSIONS, proven once.  Each exhibits the continuation the
    projection hid and says what the resume function does to it — which is
    all any rule below needs, and is why no rule ever mentions a [K]. *)

Lemma enode_tag_ret (m : M unit) :
  enode_tag m = 0%nat -> exists u : unit, m = Interface.Ret u.
Proof.
  intros Ht. destruct m as [y|T oc k]; [by exists y|].
  destruct oc; simpl in Ht; discriminate Ht.
Qed.

Lemma eread_req_at_inv (n : N) (m : M unit) (req : Interface.ReadReq.t n) :
  eread_req_at n m = Some req ->
  exists K, m = Interface.Next (Interface.MemRead n req) K /\
       forall w : bv (8 * n), eread_resume (bv_unsigned w) m = K (inl (w, None)).
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  destruct (decide (n0 = n)) as [Heq|Hne]; [|discriminate Hn].
  destruct Heq. simpl in Hn. injection Hn as <-.
  exists k. split; [reflexivity|].
  intros w. simpl. by rewrite Z_to_bv_bv_unsigned.
Qed.

Lemma ewrite_req_at_inv (n : N) (m : M unit) (req : Interface.WriteReq.t n) :
  ewrite_req_at n m = Some req ->
  exists K, m = Interface.Next (Interface.MemWrite n req) K /\
       ewrite_resume m = K (inl None).
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  destruct (decide (n0 = n)) as [Heq|Hne]; [|discriminate Hn].
  destruct Heq. simpl in Hn. injection Hn as <-.
  exists k. by split.
Qed.

Lemma ebar_at_inv (m : M unit) (b : barrier_kind) :
  ebar_at m = Some b ->
  exists K, m = Interface.Next (Interface.Barrier b) K /\ ebar_resume m = K tt.
Proof.
  intros Hn. destruct m as [y|T oc k]; [by simpl in Hn|].
  destruct oc; simpl in Hn; try discriminate Hn.
  injection Hn as <-. exists k. by split.
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
      destruct (esil_node_ecycle gen σ c D m m1 rs2 Hnode2) as (σ1 & Hc & _).
      by do 2 eexists. }
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
    iModIntro. destruct Hσ' as [->|[[-> (v & ->)]|[-> ->]]].
    - iSplitL "Hri Hcl"; [by iApply "Hcl"|]. by iApply "H".
    - (* D3: THE ANNOUNCE.  [weak_state_interp (ewg_ib σ c v)] IS
         [weak_state_interp σ] — a conversion, so the very same proof term
         that closed the σ-identity arm closes this one. *)
      iSplitL "Hri Hcl".
      { iApply weak_state_interp_reg_id. by iApply "Hcl". }
      by iApply "H".
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

  (** THE CALL-SITE FORM (the finding-F8 shape, §3b): a whole stretch of
      [EWP] out, and **NO EQUATION IN** — the successor cursor is the
      unevaluated composition [esil n D x], so nothing at the call site is
      named, computed or read back.  This is the reflective interface the
      design's "reflective batching is MANDATORY" section asks for, and it is
      what a leaf uses. *)
  Lemma ewp_ev_batch (gen : nat) (c : CPU) (D : gset register) (n : nat)
      (x : ecur) :
    gen = 0%nat ->
    ereg_frame c x.1 D -∗
    (ereg_frame c (esil n D x).1 D -∗
       EWP (ECycle gen c (esil n D x).2 None) @ ⊤) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    intros Hgen.
    exact (ewp_ev_sil_rtc gen c D (x.2, x.1) ((esil n D x).2, (esil n D x).1)
             Hgen
             (erun_silent_sound n D x.1 x.2 (esil n D x).1 (esil n D x).2
                (surjective_pairing (erun_silent n D x.1 x.2)))).
  Qed.

End batch.

(* ====================================================================== *)
(** ** 5. The RAM events

    The two rules whose leaf content is weak-memory content.  Both are stated
    at the EVENT's own state — finding (F3) in force — and both give the caller
    a mask-changing callback AROUND THE SINGLE EVENT, so an escrow invariant is
    opened and closed at that one event (finding (F5)). *)

(** [WeakPromise.read_ok] at a plain (non-coherent, non-exclusive) access IS
    [WeakInterp.wbyte_ok] per byte, at the hart's own projected [wmstate].
    Definitional; it is what lets §5c reuse [WeakBridge]'s pinning lemma. *)
Lemma read_ok_wbyte_ok (σ : wgstate) (c : CPU) (ak : akinfo) (base : Z)
    (tvs : list (nat * bv 8)) (j t : nat) (v : bv 8) :
  ak_coh ak = false -> ak_latest ak = false ->
  read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) (ak_sync ak) false base tvs ->
  tvs !! j = Some (t, v) ->
  wbyte_ok (whart_view σ c) ak (base + Z.of_nat j) t v.
Proof.
  intros Hcoh Hlat Hrd Hj. destruct (Hrd j t v Hj) as (Hb & Hrdbl & _).
  rewrite /wbyte_ok Hcoh /=. split; [exact Hb|]. split; [exact Hrdbl|].
  by rewrite Hlat.
Qed.

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

  (** *** 5c. THE FETCH — a DERIVED rule for reading NEVER-WRITTEN text
      (finding F7's answer)

      F7 measured that this model's instruction fetch is an ORDINARY PLAIN RAM
      READ ([ak_coh = ak_latest = ak_sync = false]), not an [AK_ifetch]
      coherent one — so §5b's racy-load rule applies to it, and the S5 leaves
      paid for that: one general rule application, one caller callback and one
      per-event [read_ok] justification per instruction, which was the single
      largest source of the event-granular leaves' extra cost.

      BUT KERNEL TEXT IS IMMUTABLE IN THE VERIFIED CONFIGURATION, and the tree
      already has the resource that says so: [WeakInstr.wkernel_text] is a
      big-op of [wlat_pointsto a DfracDiscarded 0 b] — PERSISTENT era-image
      elements, i.e. "the latest write to [a] is the boot image, at timestamp
      0".  [etext_word] below is that resource at ONE access window, keyed at
      the log's own [Z] addresses (the bridge from [wkernel_text] is
      [WeakEvStarted.wkernel_text_etext_word]; it is stated there so that the
      event tier does not depend on the superseded instruction-atomic files).

      WHAT THE RULE GIVES, and it is exactly the three costs deleted:

        - NO caller callback: the rule opens and closes the interpretation
          itself.  Enabledness is EXHIBITED (timestamp 0 at every byte) rather
          than demanded;
        - NO per-event [read_ok] obligation: every admissible read of a
          never-written byte is forced to timestamp 0 ([WeakBridge]'s
          [pinned_read_unwritten] + [wbyte_ok_pinned] — the pinning lemma,
          proven once, here), so the word read is EXACTLY the certified one;
        - NO φ payment: the floors a fetch moves are the text's own, and a
          never-written byte carries no obligation to any hart at any floor
          ([WeakGhost.nv_ok_unwritten]).

      THE GAP, stated precisely.  The resource does NOT say "no message ever
      writes this byte" as a temporal fact about the log's FUTURE; it says
      "no message in the CURRENT log writes it", which is what a persistent
      [wlat_pointsto _ _ 0 _] means and all this rule needs (it is applied at
      the fetch event's own σ, where the element is re-read).  A write to the
      text would have to consume the element's [DfracDiscarded] fraction and
      cannot; that is the discipline, and it is enforced by the points-to, not
      by an extra invariant. *)

  Definition etext (a : Z) (b : bv 8) : iProp Σ :=
    wlat_pointsto a DfracDiscarded 0%nat b.

  Global Instance etext_persistent a b : Persistent (etext a b).
  Proof. rewrite /etext /wlat_pointsto. apply _. Qed.

  Definition etext_word (a : Z) (n : N) (w : bv (8 * n)) : iProp Σ :=
    ([∗ list] j ∈ seq 0 (N.to_nat n), etext (a + Z.of_nat j) (nth_byte w j))%I.

  Global Instance etext_word_persistent a n w : Persistent (etext_word a n w).
  Proof. rewrite /etext_word. apply _. Qed.

  (** The hart's view after a fetch: every byte read at timestamp 0. *)
  Definition efetch_ws (ws : wstate) (aq : bool) (base : Z) (n : N) : wstate :=
    load_post_run ws aq base (replicate (N.to_nat n) 0%nat).

  Lemma efetch_ws_le ws aq base n : ws_le ws (efetch_ws ws aq base n).
  Proof. apply load_post_run_le. Qed.

  Lemma efetch_ws_relp ws aq base n :
    w_relp (efetch_ws ws aq base n) = w_relp ws.
  Proof. apply load_post_run_relp_ev. Qed.

  (** THE PINNING LEMMA, proven once: at a never-written byte, every
      admissible timestamp of a plain read is 0 and the value is the image's.
      ([WeakBridge.wbyte_ok_pinned] at [pinned_read_unwritten].) *)
  Lemma etext_byte_pin (σ : wgstate) (c : CPU) (ak : akinfo) (a : Z)
      (t : nat) (v b : bv 8) :
    ak_coh ak = false -> ak_latest ak = false ->
    latest_val (img_z (wgimg σ)) (wglog σ) a 0%nat b ->
    wbyte_ok (whart_view σ c) ak a t v ->
    t = 0%nat /\ v = b.
  Proof.
    intros Hcoh Hlat Hlv Hok.
    have Hts : latest_ts (wglog σ) a = 0%nat
      by exact (latest_val_ts _ _ _ _ _ Hlv).
    have Ht : t = latest_ts (wm_log (whart_view σ c)) a.
    { apply (wbyte_ok_pinned (whart_view σ c) ak a t v); [|exact Hok].
      intros _. apply pinned_read_unwritten. cbn [wm_log whart_view]. exact Hts. }
    cbn [wm_log whart_view] in Ht. rewrite Hts in Ht. subst t.
    split; [reflexivity|].
    destruct Hok as [Hv _]. destruct Hlv as [Hb _].
    cbn [wimg wm_img wm_log whart_view] in Hv. rewrite Hv in Hb. by injection Hb.
  Qed.

  Lemma ewp_ev_fetch (gen : nat) (c : CPU) (n : N)
      (req : Interface.ReadReq.t n)
      (K : (bv (8 * n) * option bool + Arch.abort)%type -> M unit)
      (w : bv (8 * n)) (ws : wstate) :
    gen = 0%nat ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = false ->
    etext_word (pa_z (Interface.ReadReq.pa req)) n w -∗
    hart_ws c ws -∗
    ▷ (hart_ws c (efetch_ws ws
                    (ak_sync (classify (Interface.ReadReq.access_kind req)))
                    (pa_z (Interface.ReadReq.pa req)) n) -∗
       EWP (ECycle gen c (K (inl (w, None))) None) @ ⊤) -∗
    EWP (ECycle gen c (Interface.Next (Interface.MemRead n req) K) None) @ ⊤.
  Proof.
    iIntros (Hgen Hdev Hcoh Hlatk) "#Ht Hws H".
    iApply (ewp_ecycle gen c _ None Hgen). iIntros (σ) "Hσ".
    iDestruct (weak_state_interp_mem σ c with "Hσ") as
      "(%Hbnd & %Hnv & %Hwf & Hlog & Hlat0 & Hwsa & Hcl)".
    iDestruct (hart_ws_agree with "Hwsa Hws") as %->.
    (* ---- the text's per-byte fact, off the persistent elements ---- *)
    iAssert (⌜forall j : nat, (j < N.to_nat n)%nat ->
               latest_val (img_z (wgimg σ)) (wglog σ)
                 (pa_z (Interface.ReadReq.pa req) + Z.of_nat j) 0%nat
                 (nth_byte w j)⌝)%I as %Htext.
    { rewrite bi.pure_forall. iIntros (j). rewrite bi.pure_impl. iIntros (Hj).
      iDestruct (big_sepL_lookup _ _ j j with "Ht") as "Hj";
        [by apply lookup_seq_lt|].
      by iDestruct (wlat_lookup with "Hlat0 Hj") as %Hlv. }
    set (base := pa_z (Interface.ReadReq.pa req)).
    set (aq := ak_sync (classify (Interface.ReadReq.access_kind req))).
    (* ---- ENABLEDNESS: the all-zero read is admissible ---- *)
    set (tvs0 := (fun j : nat => (0%nat, nth_byte w j)) <$> seq 0 (N.to_nat n)).
    have Hlen0 : length tvs0 = N.to_nat n
      by rewrite /tvs0 length_fmap length_seq.
    have Hlk0 : forall j : nat, (j < N.to_nat n)%nat ->
                  tvs0 !! j = Some (0%nat, nth_byte w j).
    { intros j Hj. rewrite /tvs0 list_lookup_fmap (lookup_seq_lt 0 _ j Hj) //. }
    have Hnw : forall j : nat, (j < N.to_nat n)%nat ->
                 ¬ writes_in (wglog σ) (base + Z.of_nat j) 0%nat
                     (Nat.max (load_vpre (wgws σ c) aq)
                        (coh (wgws σ c) (base + Z.of_nat j))).
    { intros j Hj Hw. destruct (Htext j Hj) as [_ Hno]. apply Hno.
      eapply writes_in_mono_hi; [|exact Hw].
      destruct (Hbnd c) as (H1 & _ & H3 & _ & H5 & _ & H7 & _ & _).
      rewrite /load_vpre.
      pose proof (H7 (base + Z.of_nat j)). destruct aq; lia. }
    have Hrd0 : read_ok (img_z (wgimg σ)) (wglog σ) (wgws σ c) aq false base tvs0.
    { intros j t v Hj.
      have Hjlt : (j < N.to_nat n)%nat
        by (apply lookup_lt_Some in Hj; lia).
      rewrite (Hlk0 j Hjlt) in Hj. injection Hj as <- <-.
      destruct (Htext j Hjlt) as [Hv _]. split_and!.
      - exact Hv.
      - split; [by exists (nth_byte w j)|exact (Hnw j Hjlt)].
      - discriminate. }
    iApply fupd_mask_intro; [set_solver|]. iIntros "Hmask".
    iSplitR.
    { iPureIntro. do 2 eexists. simpl. rewrite Hdev. split; [exact Hcoh|].
      left. split; [exact Hlatk|]. exists w, tvs0. split_and!.
      - exact Hlen0.
      - intros j Hj. rewrite list_lookup_fmap (Hlk0 j Hj) //.
      - exact Hrd0.
      - reflexivity.
      - reflexivity. }
    iNext. iIntros (e' σ') "%Hcy". iMod "Hmask" as "_".
    simpl in Hcy. rewrite Hdev in Hcy.
    destruct Hcy as (_ & [(_ & w' & tvs & Hlen & Hbytes & Hrd & -> & ->)
                         |(Hbad & _)]); [|by rewrite Hlatk in Hbad].
    (* ---- UNIQUENESS: every admissible read is the certified word ---- *)
    have Hpin : forall (j : nat) (t : nat) (v : bv 8),
        tvs !! j = Some (t, v) -> t = 0%nat /\ v = nth_byte w j.
    { intros j t v Hj.
      have Hjlt : (j < N.to_nat n)%nat by (apply lookup_lt_Some in Hj; lia).
      apply (etext_byte_pin σ c (classify (Interface.ReadReq.access_kind req))
               (base + Z.of_nat j) t v (nth_byte w j) Hcoh Hlatk
               (Htext j Hjlt)).
      exact (read_ok_wbyte_ok σ c _ base tvs j t v Hcoh Hlatk Hrd Hj). }
    have Hww : w' = w.
    { apply bv_eq_of_bytes. intros j Hj.
      have Hjlt : (j < N.to_nat n)%nat by lia.
      destruct (lookup_lt_is_Some_2 tvs j ltac:(lia)) as [[t v] Hj2].
      destruct (Hpin j t v Hj2) as [_ Hv].
      have H2 := Hbytes j Hjlt. rewrite list_lookup_fmap Hj2 in H2.
      cbn [fmap option_fmap snd] in H2. apply Some_inj in H2.
      rewrite -H2. exact Hv. }
    have Hts1 : tvs.*1 = replicate (N.to_nat n) 0%nat.
    { apply list_eq. intros j.
      destruct (decide (j < N.to_nat n)%nat) as [Hj|Hj].
      - destruct (lookup_lt_is_Some_2 tvs j ltac:(lia)) as [[t v] Hj2].
        rewrite list_lookup_fmap Hj2 /=.
        destruct (Hpin j t v Hj2) as [-> _].
        by rewrite lookup_replicate_2.
      - rewrite lookup_ge_None_2; [|rewrite length_fmap; lia].
        rewrite lookup_ge_None_2 //. rewrite length_replicate. lia. }
    subst w'. rewrite Hts1 -/(efetch_ws (wgws σ c) aq base n).
    (* ---- the φ payment: a never-written byte owes nothing ---- *)
    iMod (hart_ws_update c (wgws σ c) (wgws σ c)
            (efetch_ws (wgws σ c) aq base n) with "Hwsa Hws") as "[Hwsa Hws]".
    iModIntro. iSplitR "Hws H"; [|by iApply "H"].
    iDestruct ("Hcl" $! (efetch_ws (wgws σ c) aq base n) (wglog σ)
                 with "[%] [%] [%] [%] [%] Hlog Hlat0 Hwsa") as "Hσ".
    - reflexivity.
    - rewrite /efetch_ws. apply load_post_run_bounded; [exact (Hbnd c)|].
      apply Forall_forall. intros t Ht.
      apply elem_of_replicate in Ht as [-> _]. lia.
    - apply (nv_hart_coh_step (wglog σ) c (wgws σ c));
        [exact (no_violation_hart _ _ c Hnv)|].
      intros a Hlt. apply nv_byte_of_ok.
      destruct (coh_load_post_run_moved (wgws σ c) aq base
                  (replicate (N.to_nat n) 0%nat) a Hlt) as (j & Hj & ->).
      rewrite length_replicate in Hj.
      apply nv_ok_unwritten.
      exact (latest_val_ts _ _ _ _ _ (Htext j Hj)).
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
    destruct Hb as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
    rewrite /ws_bounded /fence_post /=. split_and!; try (simpl; lia).
    - destruct sr; [|lia]. destruct pr, pw; simpl; lia.
    - destruct sw; [|lia]. destruct pr, pw; simpl; lia.
    - intros a. exact (H7 a).
    - intros a tv Ha. exact (H8 a tv Ha).
    - intros r. exact (H9 r).
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

  (** *** 7b. The five chaining combinators (the finding-F8 form).

      Each is "ONE SMALL PROJECTION + ONE memory-event rule".  The stretch is
      advanced with [ewp_ev_batch] (n nodes, one application, NO equation),
      the event with §5's rule, and the successor cursor is handed on as the
      unevaluated composition [ecur_read v (esil nn D x)] & co.  A whole
      instruction is these chained, in the order the certification lists the
      effects; the register footprint [D] is threaded once and the residual is
      never named. *)

  Lemma ewp_ev_seq_ret (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (x : ecur) :
    gen = 0%nat ->
    enode_tag (esil nn D x).2 = 0%nat ->
    ereg_frame c x.1 D -∗
    (ereg_frame c (esil nn D x).1 D -∗ EWP (ELoop gen c) @ ⊤) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    iIntros (Hgen Htag) "Hrf H".
    iApply (ewp_ev_batch gen c D nn x Hgen with "Hrf").
    iIntros "Hrf". destruct (enode_tag_ret _ Htag) as [u Hu]. rewrite Hu.
    iApply (ewp_ev_ret gen c u Hgen). by iApply "H".
  Qed.

  Lemma ewp_ev_seq_barrier (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (x : ecur) (b : barrier_kind) (ws : wstate) :
    gen = 0%nat ->
    ebar_at (esil nn D x).2 = Some b ->
    hart_ws c ws -∗ ereg_frame c x.1 D -∗
    ▷ (hart_ws c (efence_apply ws (ebar_now b)) -∗
         ereg_frame c (esil nn D x).1 D -∗
         EWP (ECycle gen c (ecur_bar (esil nn D x)).2 (ebar_park b)) @ ⊤) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    iIntros (Hgen Hbar) "Hws Hrf H".
    destruct (ebar_at_inv _ _ Hbar) as (K & HK & Hres).
    iApply (ewp_ev_batch gen c D nn x Hgen with "Hrf").
    iIntros "Hrf". rewrite /ecur_bar /= Hres HK.
    iApply (ewp_ev_barrier gen c b K ws Hgen with "Hws").
    iNext. iIntros "Hws". by iApply ("H" with "Hws Hrf").
  Qed.

  Lemma ewp_ev_seq_store (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (x : ecur) (n : N) (req : Interface.WriteReq.t n) (ws : wstate) :
    gen = 0%nat ->
    ewrite_req_at n (esil nn D x).2 = Some req ->
    dev_addr (Interface.WriteReq.pa req) = false ->
    n <> 0%N ->
    acc_wf (Interface.WriteReq.pa req) n ->
    hart_ws c ws -∗ ereg_frame c x.1 D -∗
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
          ereg_frame c (esil nn D x).1 D -∗
          EWP (ECycle gen c (ecur_write (esil nn D x)).2 None) @ ⊤)) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    iIntros (Hgen Hnode Hdev Hn Hacc) "Hws Hrf Hk".
    destruct (ewrite_req_at_inv _ _ _ Hnode) as (K & HK & Hres).
    iApply (ewp_ev_batch gen c D nn x Hgen with "Hrf").
    iIntros "Hrf". rewrite /ecur_write /= Hres HK.
    iApply (ewp_ev_store gen c n req K ws Hgen Hdev Hn Hacc with "Hws").
    iIntros (σ) "%Hws %Hwf %Hbnd #Hlb Hlat".
    iMod ("Hk" $! σ with "[//] [//] [//] Hlb Hlat") as "Hk". iModIntro. iNext.
    iMod "Hk" as "(%Hpay & Hlat & Hcont)". iModIntro. iFrame "Hlat".
    iSplitR; [by iPureIntro|]. iIntros "Hws". by iApply ("Hcont" with "Hws Hrf").
  Qed.

  Lemma ewp_ev_seq_load (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (x : ecur) (n : N) (req : Interface.ReadReq.t n) (ws : wstate) :
    gen = 0%nat ->
    eread_req_at n (esil nn D x).2 = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = false ->
    hart_ws c ws -∗ ereg_frame c x.1 D -∗
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
               ereg_frame c (esil nn D x).1 D -∗
               EWP (ECycle gen c
                      (ecur_read (bv_unsigned w) (esil nn D x)).2 None) @ ⊤))) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    iIntros (Hgen Hnode Hdev Hcoh Hlat) "Hws Hrf Hk".
    destruct (eread_req_at_inv _ _ _ Hnode) as (K & HK & Hres).
    iApply (ewp_ev_batch gen c D nn x Hgen with "Hrf").
    iIntros "Hrf". rewrite HK.
    iApply (ewp_ev_load gen c n req K ws Hgen Hdev Hcoh Hlat with "Hws").
    iIntros (σ) "%Hws %Hwf %Hbnd #Hlb Hlat0".
    iMod ("Hk" $! σ with "[//] [//] [//] Hlb Hlat0") as "[%Hen Hk]".
    iModIntro. iSplitR; [by iPureIntro|]. iNext.
    iIntros (w tvs) "%H1 %H2 %H3".
    iMod ("Hk" $! w tvs with "[//] [//] [//]") as "(%Hpay & Hlat0 & Hcont)".
    iModIntro. iFrame "Hlat0". iSplitR; [by iPureIntro|].
    iIntros "Hws". rewrite /ecur_read /= Hres.
    by iApply ("Hcont" with "Hws Hrf").
  Qed.

  (** *** 7c. THE FETCH COMBINATOR (finding F7's answer at the leaf-facing
      altitude): the stretch, then §5c's derived rule.  Compare
      [ewp_ev_seq_load]: NO callback, NO [read_ok] obligation, NO φ payment —
      the caller hands over the persistent text and the certified word. *)
  Lemma ewp_ev_seq_fetch (gen : nat) (c : CPU) (D : gset register) (nn : nat)
      (x : ecur) (n : N) (req : Interface.ReadReq.t n) (w : bv (8 * n))
      (ws : wstate) :
    gen = 0%nat ->
    eread_req_at n (esil nn D x).2 = Some req ->
    dev_addr (Interface.ReadReq.pa req) = false ->
    ak_coh (classify (Interface.ReadReq.access_kind req)) = false ->
    ak_latest (classify (Interface.ReadReq.access_kind req)) = false ->
    etext_word (pa_z (Interface.ReadReq.pa req)) n w -∗
    hart_ws c ws -∗ ereg_frame c x.1 D -∗
    ▷ (hart_ws c (efetch_ws ws
                    (ak_sync (classify (Interface.ReadReq.access_kind req)))
                    (pa_z (Interface.ReadReq.pa req)) n) -∗
       ereg_frame c (esil nn D x).1 D -∗
       EWP (ECycle gen c
              (ecur_read (bv_unsigned w) (esil nn D x)).2 None) @ ⊤) -∗
    EWP (ECycle gen c x.2 None) @ ⊤.
  Proof.
    iIntros (Hgen Hnode Hdev Hcoh Hlat) "#Ht Hws Hrf H".
    destruct (eread_req_at_inv _ _ _ Hnode) as (K & HK & Hres).
    iApply (ewp_ev_batch gen c D nn x Hgen with "Hrf").
    iIntros "Hrf". rewrite HK.
    iApply (ewp_ev_fetch gen c n req K w ws Hgen Hdev Hcoh Hlat with "Ht Hws").
    iNext. iIntros "Hws". rewrite /ecur_read /= Hres.
    by iApply ("H" with "Hws Hrf").
  Qed.

End adapter.
