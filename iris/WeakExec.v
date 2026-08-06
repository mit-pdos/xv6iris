(** * WeakExec.v — the weak-memory lifting tower (M1c)

    The [RiscvExec.wp_exec_step] analogue over [WeakLang.weak_riscv_lang]:
    the single per-hart framing point, plus the three device-thread rules.

    THE ORACLE, AND WHY THERE ARE TWO HART RULES.

    [RiscvExec]'s contract is "the caller supplies an [exec] witness for both
    tick values; [exec_run_det]'s uniqueness half then discharges
    [wp_lift_step]'s ∀-successor obligation".  Uniqueness is FALSE for the
    weak machine by design (a load has many admissible timestamps), so the
    ∀-successor obligation has to be handed to the caller.  Two forms:

      - [wp_wrun_step] — the PRIMITIVE.  The continuation is universally
        quantified over the successors of the RELATIONAL interpreter
        ([WeakInterp.wrun]), which is literally what [wprim_step] produces.
        Premise-free, and the one the adequacy/soundness story rests on.
      - [wp_wexec_step] — the shape M2's leaves want: the continuation is
        universally quantified over the ORACLE and the successors of the
        FUNCTIONAL interpreter ([WeakInterp.wexec]), which is what a leaf
        can compute with.  It is [wp_wrun_step] plus one caller obligation,
        [wexec_covers] — "every [wrun] successor of THIS program in THIS
        state is also a [wexec] successor at some oracle".

    WHY [wexec_covers] IS A PREMISE AND NOT A LEMMA (the finding M1c owed).
    The general bridge [wrun → ∃ χ χ', wexec … χ … = Some …] is NOT provable,
    and the obstacle is exactly the one [WeakInterp]'s §8 comment names:
    [Interface.Choose], which [wrun] branches over (as [RiscvLang.run] does)
    and [wexec] rejects (as [RiscvExec.exec] does).  Nor does the caller's
    exec witness at one oracle pin the path, the way it does in the SC tree:
    a [wrun] may read a DIFFERENT admissible value than the witness did, and
    from there descend into a different subtree of the monad — possibly one
    with a [Choose] in it.  And [Choose] is genuinely reachable in principle:
    the generated model has 54 [undefined_bitvector] sites, each of which is
    a [Choose].  So the bridge holds exactly on the choice-free fragment,
    which is what [wrun_wexec] below proves — that is the sufficient
    condition a leaf discharges (over the concrete instruction it has peeled)
    to obtain [wexec_covers].

    SIMPLIFICATIONS (see [WeakGhost]'s header): single era — the rules read
    the generation off the state interpretation's [wgen_pin] rather than off
    a generation counter, and take [gen_id = 0] as a premise, so there are no
    corpse arms to tail into ([RiscvExec.wp_dead] has no analogue here yet).
*)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakLang.
Require Import WeakGhost.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The wrun/wexec bridge *)

(** The caller obligation of [wp_wexec_step]: every relational successor is
    a functional one, at SOME oracle.  (The oracle and the post-state move
    together — a different timestamp choice gives a different post-view.) *)
Definition wexec_covers (tid : option nat) {X} (m : M X) (s : wmstate) : Prop :=
  forall (x : X) (s' : wmstate), wrun tid m s x s' ->
    exists χ χ', wexec tid m χ s = Some (x, s', χ').

(** The choice-free fragment of the monad: the recursive predicate that says
    no reachable outcome is [Interface.Choose].  Same dependent-match shape
    as [wrun] itself. *)
Fixpoint mchoice_free {X} (m : M X) {struct m} : Prop :=
  match m with
  | Interface.Ret _ => True
  | Interface.Next oc k =>
      (match oc in Interface.outcome _ T return (T -> M X) -> Prop with
       | Interface.Choose _ => fun _ => False
       | _ => fun k => forall t, mchoice_free (k t)
       end) k
  end.

(** A COHERENT read has no choice either: its admissibility condition IS
    [WeakMem.latest], which pins the timestamp ([latest_ts_eq]).  The
    [ak_coh] twin of [WeakInterp.wread_all_seen], and what makes the
    fetch/walker arm of the bridge go through. *)
Lemma wread_coh_ts s ak pa n ts w :
  ak_coh ak = true -> wread_ok s ak pa n ts w -> ts = coh_ts s pa n.
Proof.
  intros Hcoh [Hlen Hbytes].
  apply (list_eq_same_length _ _ (N.to_nat n));
    [apply coh_ts_length|exact Hlen|].
  intros j t1 t2 Hj Ht1 Ht2.
  assert (Hjn : (N.of_nat j < n)%N) by lia.
  destruct (Hbytes j Hjn) as [Hv Hadm]. rewrite Hcoh in Hadm.
  assert (Hlat : latest (wimg s) (wm_log s) (acc_addr pa j) (ts !!! j)).
  { split; [by exists (nth_byte w j)|exact Hadm]. }
  rewrite (list_lookup_total_correct _ _ _ Ht1) in Hlat.
  rewrite -(latest_ts_eq _ _ _ _ Hlat).
  rewrite -(coh_ts_lookup s pa n j Hj) (list_lookup_total_correct _ _ _ Ht2) //.
Qed.

(** THE BRIDGE, on the choice-free fragment.  Every read arm is complete on
    its own ([WeakInterp.wread_bytes_complete]), so the oracle is built by
    consing the timestamps the run chose; every other arm is deterministic
    and [wexec] follows [wrun] step for step. *)
Lemma wrun_wexec tid {X} (m : M X) :
  mchoice_free m ->
  forall s x s', wrun tid m s x s' ->
    exists χ χ', wexec tid m χ s = Some (x, s', χ').
Proof.
  induction m as [y|T oc k IH]; intros Hcf s x s' Hrun.
  - destruct Hrun as [-> ->]. by exists [], [].
  - destruct oc; simpl in Hcf, Hrun;
      try (exact (IH _ (Hcf _) _ _ _ Hrun));
      try (exfalso; exact Hrun);
      try (exfalso; exact Hcf).
    + (* MemRead *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_read _ _ _) as [[w0 d']|] eqn:Hdr; [|exfalso; exact Hrun].
        destruct (IH _ (Hcf _) _ _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdr. exact Hex.
      * destruct Hrun as (w & ts & Hok & Hrun).
        destruct (IH _ (Hcf _) _ _ _ Hrun) as (χ & χ' & Hex).
        (* the request is an anonymous binder of [Interface.MemRead]; grab
           its access kind off the admissibility hypothesis *)
        lazymatch goal with
        | Hok0 : wread_ok _ ?ak _ _ _ _ |- _ => destruct (ak_coh ak) eqn:Hcoh
        end.
        -- pose proof (wread_coh_ts _ _ _ _ _ _ Hcoh Hok) as Hts.
           exists χ, χ'. simpl. rewrite Hd Hcoh -Hts.
           rewrite (wread_bytes_complete _ _ _ _ _ _ Hok). exact Hex.
        -- exists (ts :: χ), χ'. simpl. rewrite Hd Hcoh.
           rewrite (wread_bytes_complete _ _ _ _ _ _ Hok). exact Hex.
    + (* MemWrite *)
      destruct (dev_addr _) eqn:Hd.
      * destruct (dev_write _ _ _ _) as [d'|] eqn:Hdw; [|exfalso; exact Hrun].
        destruct (IH _ (Hcf _) _ _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd Hdw. exact Hex.
      * destruct (IH _ (Hcf _) _ _ _ Hrun) as (χ & χ' & Hex).
        exists χ, χ'. simpl. rewrite Hd. exact Hex.
Qed.

Lemma wexec_covers_choice_free tid {X} (m : M X) s :
  mchoice_free m -> wexec_covers tid m s.
Proof. intros Hcf x s' Hrun. by eapply wrun_wexec. Qed.

(* ====================================================================== *)
(** ** 2. The successor states of the four non-power arms

    Named so that a rule's statement, [wprim_step]'s arm and the inversion
    lemma all spell the post-state the same way. *)

Definition wg_dev (g : wgstate) (d' : dev_state) : wgstate :=
  WGState (wgregs g) (wgimg g) (wglog g) (wgws g) d' (wggen g) (wgpow g).

Definition wg_regs (g : wgstate) (gr' : CPU -> regstate) : wgstate :=
  WGState gr' (wgimg g) (wglog g) (wgws g) (wgdev g) (wggen g) (wgpow g).

Definition wg_dma (g : wgstate) (d' : dev_state) (w : gmap Arch.pa (bv 8))
    : wgstate :=
  WGState (wgregs g) (wgimg g) (wglog g ++ wmsgs_of_map w) (wgws g) d'
          (wggen g) (wgpow g).

(* ====================================================================== *)
(** ** 3. The hart rule *)

Section WeakHart.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (** THE PRIMITIVE.  The caller opens the ambient hart's view of the state
      ([wmstate_interp], i.e. [RiscvPtsto.mstate_interp] with the memory
      conjunct replaced by log + latest-write map + this hart's weak state),
      supplies ONE witness that the machine can step, and a continuation
      that must re-establish the hart interpretation at EVERY relational
      successor.  [wp_lift_step]'s tick nondeterminism rides in the
      continuation's [tick] binder exactly as in [RiscvExec.wp_exec_step]. *)
  Lemma wp_wrun_step Φ :
    gen_id = 0%nat ->
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜∃ χ σ0 χ', wexec (Some (fin_to_nat cpu_id)) (riscv_step false) χ σ
                   = Some (tt, σ0, χ')⌝ ∗
       ▷ (∀ (tick : bool) (σ' : wmstate),
            ⌜wrun (Some (fin_to_nat cpu_id)) (riscv_step tick) σ tt σ'⌝
            ={∅,⊤}=∗ wmstate_interp σ' ∗
                     WP (Loop : expr weak_riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid) "H".
    iApply (wp_lift_step (Λ := weak_riscv_lang)); first done.
    iIntros (g ns κ κs nt) "(%Hpin & %Hbnd & %Hwf & Hgr & Hdev & Hlog & Hlat & Hws)".
    destruct Hpin as [Hpow Hgen].
    assert (Hlive : wthread_live g gen_id) by (split; [exact Hpow|by rewrite Hgid]).
    iDestruct (gregs_interp_acc with "Hgr") as "[Hri Hclose]".
    iDestruct (wws_interp_acc with "Hws") as "[Hwsc Hwsclose]".
    iMod ("H" $! (whart_view g cpu_id) with "[Hri Hdev Hlog Hlat Hwsc]")
      as "(%Hred & Hk)".
    { rewrite /wmstate_interp /whart_view /=.
      iSplitR; [iPureIntro; exact (Hbnd cpu_id)|].
      iSplitR; [iPureIntro; exact Hwf|].
      iFrame "Hri Hdev Hlog Hlat Hwsc". }
    iModIntro. iSplitR.
    { iPureIntro. destruct Hred as (χ & σ0 & χ' & Hex).
      pose proof (wexec_wrun _ _ _ _ _ _ _ Hex) as Hrun.
      exists [], (LoopE gen_id cpu_id), (whart_write g cpu_id σ0), [].
      left. exists gen_id, cpu_id. split_and!; try reflexivity.
      left. split; [exact Hlive|]. by exists false, tt, σ0. }
    iIntros (e2 g2 efs Hstep) "!>".
    apply wprim_step_loop_inv in Hstep as (-> & -> & -> & Harm).
    destruct Harm as [(_ & tick & u & s' & Hrun & ->)|(Hnl & ->)];
      [|by destruct (Hnl Hlive)].
    destruct u.
    (* the era-initial image is never written, so the post-state's image IS
       the one the state interpretation holds ([WeakInterp.wrun_img]) *)
    assert (Himg : wm_img s' = wgimg g) by exact (wrun_img _ _ _ _ _ Hrun).
    (* the OTHER harts' views did not move, but the log may have grown:
       [ws_bounded] is monotone in its bound, and the log is append-only *)
    assert (Hlen : (length (wglog g) ≤ length (wm_log s'))%nat).
    { destruct (wrun_log_app _ _ _ _ _ Hrun) as (lext & Hlext).
      rewrite whart_view_log in Hlext. rewrite Hlext length_app. lia. }
    iIntros "_".
    iMod ("Hk" $! tick s' with "[//]")
      as "((%Hbnd' & %Hwf' & Hri' & Hdev' & Hlog' & Hlat' & Hwsc') & HWP)".
    assert (Hbnd2 : ∀ c : CPU,
              ws_bounded (wgws (whart_write g cpu_id s') c)
                         (length (wglog (whart_write g cpu_id s')))).
    { intros c. rewrite whart_write_log.
      destruct (decide (c = cpu_id)) as [->|Hne].
      - rewrite whart_write_ws_eq. exact Hbnd'.
      - rewrite (whart_write_ws_ne _ _ _ _ Hne).
        exact (ws_bounded_mono _ _ _ (Hbnd c) Hlen). }
    iDestruct ("Hclose" with "Hri'") as "Hgr'".
    iDestruct ("Hwsclose" with "Hwsc'") as "Hws'".
    iEval (rewrite Himg) in "Hlat'".
    iModIntro. iFrame "HWP". iSplitL; [|done].
    rewrite /weak_state_interp /=.
    iSplitR; [by iPureIntro; split|].
    iSplitR; [iPureIntro; exact Hbnd2|].
    iSplitR; [iPureIntro; rewrite whart_write_log; exact Hwf'|].
    iFrame "Hgr' Hdev' Hlog' Hlat' Hws'".
  Qed.

  (** THE LEAF-FACING FORM: the same rule with the continuation quantified
      over the ORACLE and [wexec]'s successors.  [Hcov] is the bridge
      obligation discussed in the header — dischargeable by
      [wexec_covers_choice_free] on the choice-free fragment. *)
  Lemma wp_wexec_step Φ :
    gen_id = 0%nat ->
    (∀ σ, wmstate_interp σ ={⊤,∅}=∗
       ⌜∀ tick : bool, wexec_covers (Some (fin_to_nat cpu_id))
                                    (riscv_step tick) σ⌝ ∗
       ⌜∃ χ σ0 χ', wexec (Some (fin_to_nat cpu_id)) (riscv_step false) χ σ
                   = Some (tt, σ0, χ')⌝ ∗
       ▷ (∀ (tick : bool) (χ : list (list nat)) (σ' : wmstate)
            (χ' : list (list nat)),
            ⌜wexec (Some (fin_to_nat cpu_id)) (riscv_step tick) χ σ
             = Some (tt, σ', χ')⌝
            ={∅,⊤}=∗ wmstate_interp σ' ∗
                     WP (Loop : expr weak_riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid) "H". iApply (wp_wrun_step with "[H]"); [exact Hgid|].
    iIntros (σ) "Hσ". iMod ("H" $! σ with "Hσ") as "(%Hcov & %Hred & Hk)".
    iModIntro. iSplitR; [by iPureIntro|].
    iNext. iIntros (tick σ' Hrun).
    destruct (Hcov tick tt σ' Hrun) as (χ & χ' & Hex).
    iApply ("Hk" $! tick χ σ' χ'). iPureIntro. exact Hex.
  Qed.

End WeakHart.

(* ====================================================================== *)
(** ** 4. The device threads

    Each hands the caller the WHOLE state interpretation and takes it back
    at its arm's successor: a device thread touches no per-hart resource, so
    there is nothing to focus.  The disk's arm is the only one that appends
    to the log — re-establishing [wlat_interp] across that append is the
    caller's obligation and is where M5's device-view work lands. *)

Section WeakDev.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{GEN : GenId}.

  Lemma wp_wuart_step Φ :
    gen_id = 0%nat ->
    (∀ g, weak_state_interp g ={⊤,∅}=∗
       ▷ (∀ d', ⌜uart_step (wgdev g) d'⌝ ={∅,⊤}=∗
            weak_state_interp (wg_dev g d') ∗
            WP (UartLoop : expr weak_riscv_lang) {{ Φ }})) -∗
    WP (UartLoop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid) "H".
    iApply (wp_lift_step (Λ := weak_riscv_lang)); first done.
    iIntros (g ns κ κs nt) "Hsi".
    iDestruct "Hsi" as "(%Hpin & Hrest)".
    destruct Hpin as [Hpow Hgen].
    assert (Hlive : wthread_live g gen_id) by (split; [exact Hpow|by rewrite Hgid]).
    iMod ("H" $! g with "[Hrest]") as "Hk".
    { rewrite /weak_state_interp. iSplitR; [by iPureIntro; split|]. iExact "Hrest". }
    iModIntro. iSplitR.
    { iPureIntro. exists [], (UartLoopE gen_id), g, [].
      exact (wprim_step_uart_idle gen_id g Hlive). }
    iIntros (e2 g2 efs Hstep) "!>".
    apply wprim_step_uart_inv in Hstep as (-> & -> & -> & Harm).
    destruct Harm as [(_ & d' & Hstep & ->)|(Hnl & ->)];
      [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! d' with "[//]") as "[Hsi HWP]".
    iModIntro. iFrame "HWP". iSplitL; [|done]. iExact "Hsi".
  Qed.

  Lemma wp_wplic_step Φ :
    gen_id = 0%nat ->
    (∀ g, weak_state_interp g ={⊤,∅}=∗
       ▷ (∀ gr', ⌜plic_step (wgdev g) (wgregs g) gr'⌝ ={∅,⊤}=∗
            weak_state_interp (wg_regs g gr') ∗
            WP (PlicLoop : expr weak_riscv_lang) {{ Φ }})) -∗
    WP (PlicLoop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid) "H".
    iApply (wp_lift_step (Λ := weak_riscv_lang)); first done.
    iIntros (g ns κ κs nt) "Hsi".
    iDestruct "Hsi" as "(%Hpin & Hrest)".
    destruct Hpin as [Hpow Hgen].
    assert (Hlive : wthread_live g gen_id) by (split; [exact Hpow|by rewrite Hgid]).
    iMod ("H" $! g with "[Hrest]") as "Hk".
    { rewrite /weak_state_interp. iSplitR; [by iPureIntro; split|]. iExact "Hrest". }
    iModIntro. iSplitR.
    { iPureIntro.
      exists [], (PlicLoopE gen_id),
        (wg_regs g (<[(0%fin : CPU) := register_set sig_seip
              (bool_to_bit (dev_seip (wgdev g) (fin_to_nat (0%fin : CPU))))
              (wgregs g (0%fin : CPU))]> (wgregs g))), [].
      right; right; right; left. exists gen_id. split_and!; try reflexivity.
      left. split; [exact Hlive|].
      eexists. split;
        [apply (PlicStepWire (wgdev g) (wgregs g) (0%fin : CPU))|reflexivity]. }
    iIntros (e2 g2 efs Hstep) "!>".
    apply wprim_step_plic_inv in Hstep as (-> & -> & -> & Harm).
    destruct Harm as [(_ & gr' & Hstep & ->)|(Hnl & ->)];
      [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! gr' with "[//]") as "[Hsi HWP]".
    iModIntro. iFrame "HWP". iSplitL; [|done]. iExact "Hsi".
  Qed.

  Lemma wp_wdisk_step Φ :
    gen_id = 0%nat ->
    (∀ g, weak_state_interp g ={⊤,∅}=∗
       ▷ (∀ d' w, ⌜wdisk_step (wgdev g) (wflat (wgimg g) (wglog g)) d' w⌝
            ={∅,⊤}=∗ weak_state_interp (wg_dma g d' w) ∗
                     WP (DiskLoop : expr weak_riscv_lang) {{ Φ }})) -∗
    WP (DiskLoop : expr weak_riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hgid) "H".
    iApply (wp_lift_step (Λ := weak_riscv_lang)); first done.
    iIntros (g ns κ κs nt) "Hsi".
    iDestruct "Hsi" as "(%Hpin & Hrest)".
    destruct Hpin as [Hpow Hgen].
    assert (Hlive : wthread_live g gen_id) by (split; [exact Hpow|by rewrite Hgid]).
    iMod ("H" $! g with "[Hrest]") as "Hk".
    { rewrite /weak_state_interp. iSplitR; [by iPureIntro; split|]. iExact "Hrest". }
    iModIntro. iSplitR.
    { iPureIntro. exists [], (DiskLoopE gen_id), g, [].
      exact (wprim_step_disk_idle gen_id g Hlive). }
    iIntros (e2 g2 efs Hstep) "!>".
    apply wprim_step_disk_inv in Hstep as (-> & -> & -> & Harm).
    destruct Harm as [(_ & d' & w & Hstep & ->)|(Hnl & ->)];
      [|by destruct (Hnl Hlive)].
    iIntros "_". iMod ("Hk" $! d' w with "[//]") as "[Hsi HWP]".
    iModIntro. iFrame "HWP". iSplitL; [|done]. iExact "Hsi".
  Qed.

End WeakDev.
