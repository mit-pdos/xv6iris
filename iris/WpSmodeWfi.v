(* WpSmodeWfi.v -- the [wfi] instruction leaf at the sconf tier.

   [wfi] is the only instruction in the kernel whose model semantics is
   NOT one retiring machine step, so it does not go through the
   [wp_instr_s_sconf] funnel.  The model:

     - [execute_WFI tt] at Supervisor returns [Enter_Wait WAIT_WFI];
       since [wait_is_nop WAIT_WFI = false], [try_step]'s postlude writes
       [hart_state := HART_WAITING (WAIT_WFI, instbits)] and -- the hart
       now being WAITING -- performs NEITHER [tick_pc] NOR the minstret
       bump.  So after the ENTER step PC still points at the wfi and the
       nextPC = pc+4 written by the fetch/execute bookkeeping survives.
     - every later step goes through [run_hart_waiting], which reads
       [shouldWakeForInterrupt] = [mip & mie <> 0] straight off the file
       (the branch is demonic and needs no ownership at all):
         * no wake: only the prelude's [minstret_increment] write happens;
         * wake: [hart_state := HART_ACTIVE], then the ordinary retiring
           tail -- [tick_pc] puts nextPC (= pc+4) into PC.

   PER NODE, THE LEAF IS THREE THINGS, and the first is why this file has
   a footprint of its own:

   1. [wfi_Drw] / [wfi_Dro] -- [HartSFrame]'s whole-cycle S-mode footprint
      WITH [hart_state] MOVED INTO THE WRITABLE HALF.  Every other S-mode
      cycle leaves the hart ACTIVE, so [HartSFrame] pins that cell
      read-only and its tower [s_rs] spells [HART_ACTIVE tt] outright; a
      wfi writes it TWICE.  The split is about which set a WALKER may
      write, not about ownership ([s_Df dq hart_state] is [dq]), so
      [wfi_frames_s] moves the cell between the halves for free -- which
      is what lets the ENTER step run on the existing S-mode layer at
      [s_Drw]/[s_Dro], where the hart is still ACTIVE.
   2. [wfi_wait_loop] -- the WAIT phase: a Löb over
      [HartStepFull.swp_exec_step_waiting].  The stutter arm's own later
      strips the IH; the wake arm's is spent on the caller's continuation.
      Partial correctness makes "never wakes" a perfectly good outcome, so
      nothing here is a fuel or a fairness assumption.
   3. [wfi_run_enter] -- the ENTER step's [run_hart_active], on
      [SmodeCorePt.swp_run_hart_active_gen_exf_res].  Its retiring sibling
      [spt_run_hart_active_instr_S] cannot serve: it pins RETIRE_SUCCESS
      in both the execute obligation and the Step it concludes, and wfi
      returns [Enter_Wait WAIT_WFI].  Only the two F_Base arms are
      replayed -- [instr pc false (WFI tt)] rules the RVC pair out.

   The pure [run_hart_waiting] facts are NOT restated here: they live in
   [HartStepFull] ([exec_run_hart_waiting_wake] / [_stay], [goodmb_...],
   [exec_shouldWakeForInterrupt]) and the waiting rule consumes them. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpGpr InstrBytes.
Require Import SmodeCorePt.
Require Import RiscvExtras.
Require Import CommonWalk.
Require Import UserBits.
Require Import IntrDefs.
Require Import WpDecodeBridge HartGoodb.
Require Import HartLift HartSpan HartSwp HartSFrame WpSFrames.
Require Import HartRunGen HartStepFull HartMCycle.
Require Import WpIntrInv.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* THE WFI FOOTPRINT: [HartSFrame]'s whole-cycle one WITH [hart_state]     *)
(* MOVED INTO THE WRITABLE HALF.                                          *)
(*                                                                       *)
(* [s_Drw]/[s_Dro] cannot serve a wfi.  Every other S-mode cycle leaves    *)
(* the hart ACTIVE, so [HartSFrame] pins [hart_state] read-only and its    *)
(* tower [s_rs] spells the value [HART_ACTIVE tt] outright.  A wfi writes  *)
(* that cell TWICE -- ACTIVE -> WAITING at the enter step, WAITING ->      *)
(* ACTIVE at the wake -- and both [HartStepFull.swp_exec_step_full] (whose *)
(* [Enter_Wait] arm is the enter step) and [swp_exec_step_waiting] demand  *)
(* [hart_state ∈ Drw].  The two sets are ordinary parameters of those      *)
(* rules, so the variant lives here rather than in [HartSFrame]: nothing   *)
(* else in the tree wants a hart-parking footprint.                       *)
(* ===================================================================== *)
Definition wfi_Drw : gset register :=
  {[ (R_bitvector_64 PC : register); (R_bitvector_64 nextPC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register);
     (R_bitvector_64 mcycle : register);
     (R_bitvector_64 mtime : register);
     (R_bitvector_64 mip : register);
     (tlb : register); (hart_state : register) ]}.

Definition wfi_Dro : gset register :=
  {[ (cur_privilege : register); (mstatus : register);
     (pmpcfg_n : register); (pmpaddr_n : register);
     (R_bitvector_32 mcountinhibit : register);
     (R_bitvector_64 minstretcfg : register);
     (misa : register); (mseccfg : register); (pma_regions : register);
     (htif_tohost_base : register); (elp : register); (senvcfg : register);
     (satp : register); (mie : register); (mideleg : register);
     (menvcfg : register) ]}.

Lemma wfi_disj : wfi_Drw ## wfi_Dro.
Proof. rewrite /wfi_Drw /wfi_Dro. set_solver. Qed.

Lemma wfi_union : wfi_Drw ∪ wfi_Dro = s_Drw ∪ s_Dro.
Proof. rewrite /wfi_Drw /wfi_Dro /s_Drw /s_Dro. set_solver. Qed.

Lemma wfi_w_PC : (R_bitvector_64 PC : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_ms : (R_bitvector_64 minstret : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_mi : (R_bool minstret_increment : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_cy : (R_bitvector_64 mcycle : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_ti : (R_bitvector_64 mtime : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_ip : (R_bitvector_64 mip : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_nPC : (R_bitvector_64 nextPC : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_tlb : (tlb : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_w_hart : (hart_state : register) ∈ wfi_Drw.
Proof. rewrite /wfi_Drw. set_solver. Qed.

Lemma wfi_in_PC : (R_bitvector_64 PC : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_in_nPC : (R_bitvector_64 nextPC : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_in_ms : (R_bitvector_64 minstret : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_in_mi : (R_bool minstret_increment : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_in_hart : (hart_state : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Drw. set_solver. Qed.
Lemma wfi_in_priv : (cur_privilege : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Dro. set_solver. Qed.
Lemma wfi_in_mc : (R_bitvector_32 mcountinhibit : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Dro. set_solver. Qed.
Lemma wfi_in_micfg : (R_bitvector_64 minstretcfg : register) ∈ wfi_Drw ∪ wfi_Dro.
Proof. rewrite /wfi_Dro. set_solver. Qed.

Section WfiFrames.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma wfi_rw_split (rs : regstate) :
    (hreg_frame rs wfi_Drw : iProp Σ) ⊣⊢
    ((R_bitvector_64 PC) ↦ᵣ register_lookup (R_bitvector_64 PC) rs ∗
     (R_bitvector_64 nextPC) ↦ᵣ register_lookup (R_bitvector_64 nextPC) rs ∗
     (R_bitvector_64 minstret) ↦ᵣ
       register_lookup (R_bitvector_64 minstret) rs ∗
     (R_bool minstret_increment) ↦ᵣ
       register_lookup (R_bool minstret_increment) rs ∗
     (R_bitvector_64 mcycle) ↦ᵣ register_lookup (R_bitvector_64 mcycle) rs ∗
     (R_bitvector_64 mtime) ↦ᵣ register_lookup (R_bitvector_64 mtime) rs ∗
     (R_bitvector_64 mip) ↦ᵣ register_lookup (R_bitvector_64 mip) rs ∗
     tlb ↦ᵣ register_lookup tlb rs ∗
     hart_state ↦ᵣ register_lookup hart_state rs)%I.
  Proof.
    rewrite /hreg_frame /wfi_Drw.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma wfi_ro_split (dq : dfrac) (rs : regstate) :
    (hreg_frame_ro (s_Df dq) rs wfi_Dro : iProp Σ) ⊣⊢
    (reg_pointsto cur_privilege dq (register_lookup cur_privilege rs) ∗
     reg_pointsto mstatus dq (register_lookup mstatus rs) ∗
     reg_pointsto pmpcfg_n dq (register_lookup pmpcfg_n rs) ∗
     reg_pointsto pmpaddr_n dq (register_lookup pmpaddr_n rs) ∗
     reg_pointsto (R_bitvector_32 mcountinhibit) DfracDiscarded
       (register_lookup (R_bitvector_32 mcountinhibit) rs) ∗
     reg_pointsto (R_bitvector_64 minstretcfg) DfracDiscarded
       (register_lookup (R_bitvector_64 minstretcfg) rs) ∗
     reg_pointsto misa DfracDiscarded (register_lookup misa rs) ∗
     reg_pointsto mseccfg DfracDiscarded (register_lookup mseccfg rs) ∗
     reg_pointsto pma_regions DfracDiscarded
       (register_lookup pma_regions rs) ∗
     reg_pointsto htif_tohost_base DfracDiscarded
       (register_lookup htif_tohost_base rs) ∗
     reg_pointsto elp DfracDiscarded (register_lookup elp rs) ∗
     reg_pointsto senvcfg DfracDiscarded (register_lookup senvcfg rs) ∗
     reg_pointsto satp dq (register_lookup satp rs) ∗
     reg_pointsto mie dq (register_lookup mie rs) ∗
     reg_pointsto mideleg dq (register_lookup mideleg rs) ∗
     reg_pointsto menvcfg dq (register_lookup menvcfg rs))%I.
  Proof.
    rewrite /hreg_frame_ro /wfi_Dro.
    repeat (rewrite big_sepS_union; last set_solver).
    rewrite !big_sepS_singleton.
    rewrite !(s_Df_misa dq) !(s_Df_sec dq) !(s_Df_pma dq) !(s_Df_htif dq)
      !(s_Df_elp dq) !(s_Df_senv dq) !(s_Df_mc dq) !(s_Df_micfg dq).
    unfold s_Df.
    repeat (rewrite decide_False; [|discriminate]).
    by rewrite !bi.sep_assoc.
  Qed.

  Lemma wfi_agree_rw (rs rs' : regstate) :
    reg_agree_on (wfi_Drw ∪ wfi_Dro) rs rs' -> reg_agree_on wfi_Drw rs rs'.
  Proof. intros Hag r Hr. apply Hag. set_solver. Qed.

  Lemma wfi_agree_ro (rs rs' : regstate) :
    reg_agree_on (wfi_Drw ∪ wfi_Dro) rs rs' -> reg_agree_on wfi_Dro rs rs'.
  Proof. intros Hag r Hr. apply Hag. set_solver. Qed.

  Lemma wfi_rw_ext (rs rs' : regstate) :
    reg_agree_on (wfi_Drw ∪ wfi_Dro) rs rs' ->
    hreg_frame rs wfi_Drw -∗ (hreg_frame rs' wfi_Drw : iProp Σ).
  Proof.
    intros Hag. rewrite (hreg_frame_ext _ _ wfi_Drw (wfi_agree_rw _ _ Hag)).
    iIntros "H". iExact "H".
  Qed.

  Lemma wfi_ro_ext (dq : dfrac) (rs rs' : regstate) :
    reg_agree_on (wfi_Drw ∪ wfi_Dro) rs rs' ->
    hreg_frame_ro (s_Df dq) rs wfi_Dro -∗
    (hreg_frame_ro (s_Df dq) rs' wfi_Dro : iProp Σ).
  Proof.
    intros Hag.
    rewrite (hreg_frame_ro_ext _ _ _ wfi_Dro (wfi_agree_ro _ _ Hag)).
    iIntros "H". iExact "H".
  Qed.

End WfiFrames.

(* ===================================================================== *)
(* THE WAIT PHASE.                                                        *)
(* ===================================================================== *)

(* the cells a parked wfi's cycles may move: the hart's own state, the PC   *)
(* the wake ticks, the two counter cells, and the three clock cells.       *)
Definition wfi_moved : gset register :=
  {[ (hart_state : register); (R_bitvector_64 PC : register);
     (R_bitvector_64 minstret : register);
     (R_bool minstret_increment : register) ]} ∪ tk_clock3.

(* what a STUTTER leaves: still parked, PC untouched, everything else off
   the moved set unchanged. *)
Definition wfi_stay (ib : SailStdpp.Values.mword 32) (rs rs3 : regstate)
    : Prop :=
  register_lookup hart_state rs3 = HART_WAITING (WAIT_WFI, ib) /\
  register_lookup (R_bitvector_64 PC) rs3
    = register_lookup (R_bitvector_64 PC) rs /\
  reg_agree_on ((wfi_Drw ∪ wfi_Dro) ∖ wfi_moved) rs3 rs.

(* what a WAKE leaves: ACTIVE, and the PC has taken the parked nextPC. *)
Definition wfi_wake (rs rs3 : regstate) : Prop :=
  register_lookup hart_state rs3 = HART_ACTIVE tt /\
  register_lookup (R_bitvector_64 PC) rs3
    = register_lookup (R_bitvector_64 nextPC) rs /\
  reg_agree_on ((wfi_Drw ∪ wfi_Dro) ∖ wfi_moved) rs3 rs.

Lemma wfi_nPC_unmoved :
  (R_bitvector_64 nextPC : register) ∈ (wfi_Drw ∪ wfi_Dro) ∖ wfi_moved.
Proof.
  rewrite /wfi_Drw /wfi_moved /tk_clock3.
  apply elem_of_difference. split; [set_solver|].
  intros H. repeat (apply elem_of_union in H as [H|H]);
    apply elem_of_singleton in H; discriminate.
Qed.

Lemma wfi_nPC_unmoved_clock :
  (R_bitvector_64 nextPC : register) ∈ (wfi_Drw ∪ wfi_Dro) ∖ tk_clock3.
Proof.
  apply elem_of_difference. split; [apply wfi_in_nPC|].
  intros H. rewrite /tk_clock3 in H.
  repeat (apply elem_of_union in H as [H|H]);
    apply elem_of_singleton in H; discriminate.
Qed.

Lemma wfi_wake_trans (ib : SailStdpp.Values.mword 32) (rs rs3 rs4 : regstate) :
  wfi_stay ib rs rs3 -> wfi_wake rs3 rs4 -> wfi_wake rs rs4.
Proof.
  intros (_ & _ & Hag1) (Hh & Hpc & Hag2). split_and!.
  - exact Hh.
  - rewrite Hpc. exact (Hag1 _ wfi_nPC_unmoved).
  - intros r Hr. rewrite (Hag2 r Hr). exact (Hag1 r Hr).
Qed.

Lemma wfi_beq_false (r X : register) : r <> X -> register_beq r X = false.
Proof.
  intros Hne. destruct (register_beq r X) eqn:E; [| reflexivity].
  apply register_beq_eq in E. congruence.
Qed.

Lemma wfi_unmoved_ne (r : register) :
  r ∈ (wfi_Drw ∪ wfi_Dro) ∖ wfi_moved ->
  r <> (hart_state : register) /\ r <> (R_bitvector_64 PC : register) /\
  r <> (R_bitvector_64 minstret : register) /\
  r <> (R_bool minstret_increment : register).
Proof.
  intros Hr. apply elem_of_difference in Hr as [_ Hn].
  rewrite /wfi_moved in Hn. split_and!; intros ->; apply Hn; set_solver.
Qed.

Lemma wfi_unmoved_in (r : register) :
  r ∈ (wfi_Drw ∪ wfi_Dro) ∖ wfi_moved -> r ∈ wfi_Drw ∪ wfi_Dro.
Proof. intros Hr. by apply elem_of_difference in Hr as [Hr _]. Qed.

Lemma wfi_unmoved_noclock (r : register) :
  r ∈ (wfi_Drw ∪ wfi_Dro) ∖ wfi_moved ->
  r ∈ (wfi_Drw ∪ wfi_Dro) ∖ tk_clock3.
Proof.
  intros Hr. apply elem_of_difference in Hr as [Hi Hn].
  apply elem_of_difference. split; [exact Hi|].
  intros Hc. apply Hn. rewrite /wfi_moved. set_solver.
Qed.

Lemma wfi_hart_noclock :
  (hart_state : register) ∈ (wfi_Drw ∪ wfi_Dro) ∖ tk_clock3.
Proof.
  apply elem_of_difference. split; [apply wfi_in_hart|].
  intros H. rewrite /tk_clock3 in H.
  repeat (apply elem_of_union in H as [H|H]);
    apply elem_of_singleton in H; discriminate.
Qed.

Lemma wfi_PC_noclock :
  (R_bitvector_64 PC : register) ∈ (wfi_Drw ∪ wfi_Dro) ∖ tk_clock3.
Proof.
  apply elem_of_difference. split; [apply wfi_in_PC|].
  intros H. rewrite /tk_clock3 in H.
  repeat (apply elem_of_union in H as [H|H]);
    apply elem_of_singleton in H; discriminate.
Qed.

Lemma wfi_wait_cases (ib : SailStdpp.Values.mword 32) (rs rsP rs3 : regstate) :
  register_lookup hart_state rs = HART_WAITING (WAIT_WFI, ib) ->
  wait_post (wfi_Drw ∪ wfi_Dro) rs rsP ->
  reg_agree_on ((wfi_Drw ∪ wfi_Dro) ∖ tk_clock3) rs3 rsP ->
  wfi_stay ib rs rs3 \/ wfi_wake rs rs3.
Proof.
  intros Hhart Hwp Hag3.
  (* the four [wrap_pre]/[wrap_post] side conditions, POSED: an [ltac:] in
     argument position runs before the register argument is solved. *)
  assert (Hmi_hs : register_beq (hart_state : register)
                     (R_bool minstret_increment) = false)
    by (apply wfi_beq_false; discriminate).
  assert (Hmi_pc : register_beq (R_bitvector_64 PC : register)
                     (R_bool minstret_increment) = false)
    by (apply wfi_beq_false; discriminate).
  assert (Hmi_np : register_beq (R_bitvector_64 nextPC : register)
                     (R_bool minstret_increment) = false)
    by (apply wfi_beq_false; discriminate).
  assert (Hms_hs : register_beq (hart_state : register)
                     (R_bitvector_64 minstret) = false)
    by (apply wfi_beq_false; discriminate).
  assert (Hpc_hs : register_beq (hart_state : register)
                     (R_bitvector_64 PC) = false)
    by (apply wfi_beq_false; discriminate).
  assert (Hnp_hs : register_beq (R_bitvector_64 nextPC : register)
                     hart_state = false)
    by (apply wfi_beq_false; discriminate).
  destruct Hwp as [Hstay | (rs' & mi & Hag & ->)].
  - (* ---- STUTTER: the whole cycle is the prelude's one write ---- *)
    left. split_and!.
    + rewrite (Hag3 _ wfi_hart_noclock) (Hstay _ wfi_in_hart)
        (wrap_pre_other (hart_state : register) rs Hmi_hs).
      exact Hhart.
    + rewrite (Hag3 _ wfi_PC_noclock) (Hstay _ wfi_in_PC)
        (wrap_pre_other (R_bitvector_64 PC : register) rs Hmi_pc).
      reflexivity.
    + intros r Hr.
      destruct (wfi_unmoved_ne r Hr) as (_ & _ & _ & Hmi).
      rewrite (Hag3 r (wfi_unmoved_noclock r Hr))
        (Hstay r (wfi_unmoved_in r Hr))
        (wrap_pre_other r rs (wfi_beq_false _ _ Hmi)).
      reflexivity.
  - (* ---- WAKE: hart_state := ACTIVE, then the ordinary retiring tail ---- *)
    right. split_and!.
    + rewrite (Hag3 _ wfi_hart_noclock)
        (wrap_post_other (hart_state : register) rs' mi Hms_hs Hpc_hs)
        (Hag _ wfi_in_hart) register_lookup_set.
      reflexivity.
    + rewrite (Hag3 _ wfi_PC_noclock) (wrap_post_PC rs' mi)
        (Hag _ wfi_in_nPC)
        (irrelevant_register_set (R_bitvector_64 nextPC : register)
           (hart_state : register) _ _ Hnp_hs)
        (wrap_pre_other (R_bitvector_64 nextPC : register) rs Hmi_np).
      reflexivity.
    + intros r Hr.
      destruct (wfi_unmoved_ne r Hr) as (Hhs & Hpc & Hms & Hmi).
      rewrite (Hag3 r (wfi_unmoved_noclock r Hr))
        (wrap_post_other r rs' mi (wfi_beq_false _ _ Hms)
           (wfi_beq_false _ _ Hpc))
        (Hag r (wfi_unmoved_in r Hr))
        (irrelevant_register_set r (hart_state : register) _ _
           (wfi_beq_false _ _ Hhs))
        (wrap_pre_other r rs (wfi_beq_false _ _ Hmi)).
      reflexivity.
Qed.

Section WfiWait.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Definition wfi_Dr : register -> bool := fun r =>
    orb (register_beq r (R_bitvector_64 mip))
        (register_beq r (R_bitvector_64 mie)).

  Definition wfi_Dw : register -> bool := fun r =>
    register_beq r (hart_state : register).

  Lemma wfi_Dr_in (r : register) : wfi_Dr r = true -> r ∈ wfi_Drw ∪ wfi_Dro.
  Proof.
    unfold wfi_Dr. intros Hr.
    apply orb_true_elim in Hr as [Hr|Hr]; apply register_beq_eq in Hr; subst r;
      rewrite /wfi_Drw /wfi_Dro; set_solver.
  Qed.

  Lemma wfi_Dw_in (r : register) : wfi_Dw r = true -> r ∈ wfi_Drw.
  Proof.
    unfold wfi_Dw. intros Hr. apply register_beq_eq in Hr; subst r.
    apply wfi_w_hart.
  Qed.

  Lemma wfi_Dr_mip : wfi_Dr (R_bitvector_64 mip) = true.
  Proof. unfold wfi_Dr. vm_compute. reflexivity. Qed.
  Lemma wfi_Dr_mie : wfi_Dr (R_bitvector_64 mie) = true.
  Proof. unfold wfi_Dr. vm_compute. reflexivity. Qed.
  Lemma wfi_Dw_hart : wfi_Dw (hart_state : register) = true.
  Proof. unfold wfi_Dw. vm_compute. reflexivity. Qed.

  (* ------------------------------------------------------------------- *)
  (* THE WAIT LOOP.  A Löb induction over [swp_exec_step_waiting]: the     *)
  (* STUTTER arm's own later strips the IH, the WAKE arm's is spent on the *)
  (* caller's continuation.  Partial correctness makes "never wakes" a     *)
  (* perfectly good outcome, which is why nothing here is a fuel or a      *)
  (* fairness assumption.                                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wfi_wait_loop (ib : SailStdpp.Values.mword 32) (Psi : iProp Σ)
      (rs : regstate) :
    register_lookup hart_state rs = HART_WAITING (WAIT_WFI, ib) ->
    gen_cert -∗
    resv_any cpu_id -∗
    hreg_frame rs wfi_Drw -∗
    hreg_frame_ro (s_Df (DfracOwn 1)) rs wfi_Dro -∗
    Psi -∗
    (∀ rs3 : regstate, ⌜wfi_wake rs rs3⌝ -∗
       hreg_frame rs3 wfi_Drw -∗
       hreg_frame_ro (s_Df (DfracOwn 1)) rs3 wfi_Dro -∗
       resv_any cpu_id -∗ Psi -∗ WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hhart) "#Hcert Hany Hrw Hro HPsi Hcont".
    iRevert "Hany Hrw Hro HPsi Hcont". iRevert (rs Hhart).
    iLöb as "IH".
    iIntros (rs Hhart) "Hany Hrw Hro HPsi Hcont".
    iApply (swp_exec_step_waiting wfi_Dr wfi_Dw wfi_Drw wfi_Dro
              (s_Df (DfracOwn 1)) rs WAIT_WFI ib Psi
              wfi_disj wfi_Dr_in wfi_Dw_in wfi_Dr_mip wfi_Dr_mie wfi_Dw_hart
              wfi_w_cy wfi_w_ti wfi_w_ip wfi_in_priv wfi_in_hart wfi_in_mc
              wfi_in_micfg wfi_w_mi wfi_in_mi wfi_w_ms wfi_in_ms wfi_w_PC
              wfi_in_PC wfi_in_nPC Hhart
              with "Hcert Hany Hrw Hro HPsi [Hcont]").
    iNext. iIntros (rs3) "%Hag Hrw Hro Hany HPsi".
    destruct Hag as (rsP & Hwp & Hag3).
    destruct (wfi_wait_cases ib rs rsP rs3 Hhart Hwp Hag3) as [Hstay | Hwake].
    - (* ---- STUTTER: back into the loop at the landing file ---- *)
      pose proof Hstay as Hstay'. destruct Hstay' as (Hhart3 & _ & _).
      iApply ("IH" $! rs3 with "[%] Hany Hrw Hro HPsi [Hcont]").
      { exact Hhart3. }
      iIntros (rs4) "%Hw4 Hrw Hro Hany HPsi".
      iApply ("Hcont" $! rs4 with "[%] Hrw Hro Hany HPsi").
      exact (wfi_wake_trans ib rs rs3 rs4 Hstay Hw4).
    - (* ---- WAKE: the parked wfi retires at nextPC ---- *)
      iApply ("Hcont" $! rs3 with "[%] Hrw Hro Hany HPsi"). exact Hwake.
  Qed.

End WfiWait.

Section WfiBridge.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma s_Df_hart (dq : dfrac) : s_Df dq (hart_state : register) = dq.
  Proof.
    unfold s_Df. repeat (rewrite decide_False; [|discriminate]). reflexivity.
  Qed.

  (* THE TWO PRESENTATIONS OF THE SAME 25 CELLS.  [s_Df dq hart_state] is
     [dq], so [HartSFrame]'s read-only half owns [hart_state] OUTRIGHT --
     the [Drw]/[Dro] split is about which set a WALKER may write, not about
     ownership.  Moving the cell between the halves is therefore free, and
     that is what lets the wfi cycle run its enter step on the existing
     S-mode run layer (at [s_Drw]/[s_Dro], where the hart is still ACTIVE)
     and its two hart_state writes on [wfi_Drw]/[wfi_Dro]. *)
  Lemma wfi_frames_s (rs : regstate) :
    (hreg_frame rs wfi_Drw ∗
     hreg_frame_ro (s_Df (DfracOwn 1)) rs wfi_Dro : iProp Σ)
    ⊣⊢ (hreg_frame rs s_Drw ∗
        hreg_frame_ro (s_Df (DfracOwn 1)) rs s_Dro).
  Proof.
    rewrite wfi_rw_split wfi_ro_split s_rw_split s_ro_split.
    iSplit.
    - iIntros "((?&?&?&?&?&?&?&?&?) & (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?))".
      iFrame.
    - iIntros "((?&?&?&?&?&?&?&?) & (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?))".
      iFrame.
  Qed.

End WfiBridge.

(* ===================================================================== *)
(* THE ENTER STEP'S RUN LAYER.                                            *)
(*                                                                       *)
(* [SmodeCorePt.spt_run_hart_active_instr_S] is the S-mode four-arm fetch  *)
(* dispatch, but it is RETIRE-ONLY.  wfi returns [Enter_Wait WAIT_WFI], so *)
(* the two F_Base arms are replayed here on the result-generic rule        *)
(* [swp_run_hart_active_gen_exf_res].  The RVC pair is absent on purpose:  *)
(* [instr pc false (WFI tt)] pins the fetch to [F_Base w].                 *)
(* ===================================================================== *)
Section WfiRun.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context (Df : register -> dfrac).
  Context (pc ms : SailStdpp.Values.mword 64) (bmi : bool)
          (cy ti ip mst0 : SailStdpp.Values.mword 64)
          (pcfg : type_of_register pmpcfg_n)
          (paddr : type_of_register pmpaddr_n)
          (mc : SailStdpp.Values.mword 32)
          (micfg misa0 mseccfg0 senv0 : SailStdpp.Values.mword 64)
          (pmar0 : list PMA_Region) (elp0 : type_of_register elp)
          (satp0 mie0 mdv0 menv0 : SailStdpp.Values.mword 64).
  Context (Res : type_of_register tlb -> iProp Σ).

  Local Notation srs tv :=
    (s_rs pc pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
       senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 tv).

  Local Notation Qtow :=
    (fun rsx : regstate => exists tv : type_of_register tlb, rsx = srs tv).

  Local Notation RtowW W :=
    (fun rsx : regstate =>
       (W ∗ Res (register_lookup tlb rsx) ∗ resv_any cpu_id)%I).

  Local Ltac srs_lk :=
    by rewrite ?s_rs_PC ?s_rs_nPC ?s_rs_ms ?s_rs_mi ?s_rs_cy ?s_rs_ti
       ?s_rs_ip ?s_rs_tlb ?s_rs_priv ?s_rs_mst ?s_rs_hart ?s_rs_pcfg
       ?s_rs_paddr ?s_rs_mc ?s_rs_micfg ?s_rs_misa ?s_rs_sec ?s_rs_pma
       ?s_rs_htif ?s_rs_elp ?s_rs_senv ?s_rs_satp ?s_rs_mie ?s_rs_mdl
       ?s_rs_menv.

  Local Lemma wfi_decode_ok (tv : type_of_register tlb) :
    misa0 = MISA_C -> menv0 = MENVCFG_S ->
    decode_ok (s_Drw ∪ s_Dro) (srs tv).
  Proof.
    intros Hmisa Hmenv. rewrite /decode_ok. split_and!.
    - exact s_in_priv.
    - exact s_in_misa.
    - rewrite s_rs_priv. vm_compute. reflexivity.
    - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
    - rewrite s_rs_misa Hmisa. vm_compute. reflexivity.
    - rewrite s_rs_misa. exact Hmisa.
    - right. split_and!.
      + exact s_in_menv.
      + srs_lk.
      + rewrite s_rs_menv. exact Hmenv.
  Qed.

  Local Notation TRO :=
    (spt_tr_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
       mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res).

  Local Notation DISPO tv :=
    (spt_disp_obl Df pc ms bmi cy ti ip mst0 pcfg paddr mc micfg misa0
       mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0 Res tv).

  (* the execute obligation at an ARBITRARY result -- [spt_ex_obl]'s twin
     with [RETIRE_SUCCESS] replaced, which is the whole of what wfi needs
     that the retiring layer cannot say. *)
  Definition wfi_ex_obl (i : instruction) (resf : ExecutionResult)
      (Q : regstate -> Prop) (Rr : regstate -> iProp Σ) (W : iProp Σ)
    : iProp Σ :=
    (∀ tv' : type_of_register tlb,
       W -∗ Res tv' -∗ resv_any cpu_id -∗
       hreg_frame (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc 4) (srs tv')) s_Drw -∗
       hreg_frame_ro Df (register_set (R_bitvector_64 nextPC)
           (add_vec_int pc 4) (srs tv')) s_Dro -∗
       swp (execute i)
         (fun e => ⌜e = resf⌝ ∗
                   ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                   hreg_frame rs2 s_Drw ∗ hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))%I.

  Lemma wfi_run_enter (tlbv : type_of_register tlb) (i : instruction)
      (resf : ExecutionResult) (Q : regstate -> Prop)
      (Rr : regstate -> iProp Σ) (W : iProp Σ) :
    (match resf with
     | ExecuteAs other_inst =>
         (liftR (execute other_inst) : MR Step ExecutionResult)
     | result' => returnR Step result'
     end) = returnR Step resf ->
    misa0 = MISA_C ->
    menv0 = MENVCFG_S ->
    eq_vec elp0 (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Mstatus_SIE mst0) ('b"1") = false ->
    and_vec mie0 (not_vec mdv0) = zeros' 64 ->
    pma_allows_ram pmar0 ->
    pmpAddrMatchType_encdec_backwards
      (_get_Pmpcfg_ent_A (vec_access_dec pcfg 0)) = TOR ->
    zopz0zKzJ_u (zeros' 64) (vec_access_dec paddr 0) = false ->
    eq_vec (_get_Pmpcfg_ent_X (vec_access_dec pcfg 0)) ('b"1") = true ->
    (ram_base + ram_size <= uint (vec_access_dec paddr 0) * 4)%Z ->
    gen_cert -∗
    instr pc false i -∗
    W -∗
    resv_frag cpu_id None -∗
    Res tlbv -∗
    hreg_frame (srs tlbv) s_Drw -∗
    hreg_frame_ro Df (srs tlbv) s_Dro -∗
    TRO -∗
    wfi_ex_obl i resf Q Rr W -∗
    swp (run_hart_active 0)
      (fun st => ∃ w : SailStdpp.Values.mword 32,
                   ⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗
                   ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                   hreg_frame rs2 s_Drw ∗
                   hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2).
  Proof.
    intros Hplain Hmisa Hmenv Help HSIE Hmm Hpallow HA Hord HX Hcov.
    iIntros "#Hcert Hinstr HW Hfrag0 HRes Hrw Hro #Htr Hex".
    iDestruct (spt_dispatch_none Df pc ms bmi cy ti ip mst0 pcfg paddr mc
                 micfg misa0 mseccfg0 senv0 pmar0 elp0 satp0 mie0 mdv0 menv0
                 Res tlbv W (fun _ _ => False%I) Hmisa HSIE Hmm
                 with "Hcert") as "Hdisp".
    iAssert ((W ∗ Res tlbv ∗ resv_frag cpu_id None) -∗
             hreg_frame (srs tlbv) s_Drw -∗
             hreg_frame_ro Df (srs tlbv) s_Dro -∗
             swp (dispatchInterrupt Supervisor)
               (fun o => match o with
                         | Some (ii, pr) => False%I
                         | None => (W ∗ Res tlbv ∗ resv_frag cpu_id None) ∗
                                   hreg_frame (srs tlbv) s_Drw ∗
                                   hreg_frame_ro Df (srs tlbv) s_Dro
                         end))%I with "[Hdisp]" as "Hdisp'".
    { iIntros "(HW & HRes & Hfrag) Hrw Hro".
      iApply (swp_mono with "[] [-]");
        [| iApply ("Hdisp" with "HW HRes Hfrag Hrw Hro") ].
      iIntros (o). destruct o as [[ii pr] |].
      - iIntros "H". iExact "H".
      - iIntros "(HW & HRes & Hfrag & Hrw & Hro)". iFrame. }
    iDestruct "Hinstr" as "(%Hlpi & Hib)".
    iDestruct "Hib" as (r) "(%Hrvc & Hbytes & %Hdec)".
    iEval (rewrite /instr_bytes) in "Hbytes".
    iDestruct "Hbytes" as "[%H2al Hbytes]".
    pose proof (fun tv : type_of_register tlb =>
                  hfrun_lpad (s_Drw ∪ s_Dro) s_Drw (srs tv) s_in_elp
                    ltac:(rewrite s_rs_elp; exact Help)) as Hlp.
    destruct r as [e | w | h | erx];
      [ done | | cbn [fetch_is_rvc] in Hrvc; discriminate | done ].
    cbn [fetch_is_rvc decode_fetch] in Hrvc, Hdec.
    iDestruct "Hbytes" as "[%HnotRVC #Hb]".
    (* the two live arms: the fetch is one 4-byte read at a 4-aligned pc,
       two halfword reads (and two translations) at 2 mod 4. *)
    destruct (is_aligned_vaddr (Virtaddr pc) 4) eqn:Hal.
    - (* ---- 4-aligned: one 4-byte read ---- *)
      destruct (align4_low_bits pc Hal) as [Hbit0 Hbit1].
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite pa_add_0) in "Hb0".
      iDestruct (code_text with "Hb0") as (ppn) "(#Hk & _ & %Hid)".
      iDestruct (text_canonical with "Hb0") as %Hcan.
      pose proof (off4_bound pc Hal) as Hoff.
      rewrite (uint_unsigned_n _) in Hoff.
      iDestruct (s_chunk_ram pc pc 0 4 4 (nth_byte w) ppn
                   ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                   with "Hk Hb") as %[Hram0 Hram3].
      iApply (swp_mono (run_hart_active 0)
                (fun st => ((∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗
                               False) ∨
                            (⌜st = Step_Execute (resf, zero_extend' 32 w)⌝ ∗
                             ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                             hreg_frame rs2 s_Drw ∗
                             hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))%I)
                _ with "[] [-]").
      { iIntros (st) "[Hi | (-> & Hr)]"; [ iDestruct "Hi" as (ii pr) "(_ & [])" | ].
        iExists w. by iFrame. }
      iApply (swp_run_hart_active_gen_exf_res s_Drw s_Dro Df (srs tlbv)
                Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I
                Supervisor pc w i 8 Rr (fun _ _ => False%I) resf
                Hplain s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk)
                ltac:(intros rsf (tv & ->); srs_lk)
                ltac:(intros rsf (tv & ->);
                      exact (Hdec _ _ _ (wfi_decode_ok tv Hmisa Hmenv)))
                ltac:(intros rsf (tv & ->); exact (Hlp tv))
                with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
      2:{ iIntros (rsf) "%HQ (HW & HRes & Hany) Hrw Hro".
          destruct HQ as (tv & ->). rewrite s_rs_tlb.
          iApply ("Hex" $! tv with "HW HRes Hany Hrw Hro"). }
      iIntros "(HW & HRes & Hany) Hrw Hro".
      iApply (swp_mono with "[] [-]");
        [| iApply (spt_fetch_S_P s_Drw s_Dro Df (srs tlbv) Qtow (RtowW W) pc
                     (pa_of ppn pc) w s_disj s_in_PC s_in_mst s_in_priv
                     ltac:(srs_lk) ltac:(intros rsf (tv & ->); srs_lk)
                     Hbit0 Hbit1 Hal
                     with "Hcert Hrw Hro [Hany HRes HW] []") ].
      + iIntros (rr) "(%Hr & Hf)". rewrite HnotRVC in Hr. subst rr. by iFrame.
      + iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
        iApply (swp_mono with "[HW] [-]");
          [| iApply ("Htr" $! pc ppn tlbv None with
                       "[%] [%] Hk Hfrag HRes Hrw Hro") ].
        2:{ exact Hcan. }
        2:{ exact Hid. }
        iIntros (v) "(-> & Hf)". iSplitR; [done|].
        iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
        iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
        rewrite s_rs_tlb. iFrame.
      + iIntros (rsf) "%HQ Hrw Hro". destruct HQ as (tv & ->).
        iApply (swp_checked_mem_read_ifetch4_S s_Drw s_Dro Df (srs tv)
                  (pa_of ppn pc) pmar0 pcfg paddr w s_disj s_in_pma
                  s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                  ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                  HA Hord HX Hcov Hpallow Hram0 Hram3
                  (pa4_aligned ppn pc Hal) with "Hcert Hrw Hro []").
        iApply (s_text_obl pc pc 0%nat 4%nat 4%N (nth_byte w) ppn w
                  ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoff Hcan
                  (fun j _ => eq_refl) with "Hk Hb").
    - (* ---- 2 mod 4: two halfword reads, two translations ---- *)
      destruct (align2_not4_facts pc H2al Hal) as (_ & Hbit0 & Hbit1).
      assert (Hvah2 : is_aligned_vaddr (Virtaddr (add_vec_int pc 2)) 2 = true).
      { pose proof (align2_plus2 pc H2al) as Hh. rewrite fetch_pa_id in Hh.
        exact Hh. }
      assert (HbaseH : forall k : nat,
                pa_add pc (2 + k)%nat = pa_add (add_vec_int pc 2) k).
      { intros k. unfold pa_add. rewrite avi_assoc. f_equal. lia. }
      iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hb") as "#Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iEval (rewrite pa_add_0) in "Hb0".
      iDestruct (code_text with "Hb0") as (ppnl) "(#Hkl & _ & %Hidl)".
      iDestruct (text_canonical with "Hb0") as %Hcanl.
      pose proof (off_bound_div pc 2 ltac:(lia) ltac:(exists 2048; lia) H2al)
        as Hoffl. rewrite (uint_unsigned_n _) in Hoffl.
      iDestruct (big_sepL_lookup _ _ 2%nat 2%nat with "Hb") as "#Hb2".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (code_text with "Hb2") as (ppnh) "(#Hkh & _ & %Hidh)".
      iDestruct (text_canonical with "Hb2") as %Hcanh.
      pose proof (off_bound_div (add_vec_int pc 2) 2 ltac:(lia)
                    ltac:(exists 2048; lia) Hvah2) as Hoffh.
      rewrite (uint_unsigned_n _) in Hoffh.
      iDestruct (s_chunk_ram pc pc 0 2 4 (nth_byte w) ppnl
                   ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                   with "Hkl Hb") as %[Hraml0 Hraml1].
      iDestruct (s_chunk_ram pc (add_vec_int pc 2) 2 2 4 (nth_byte w) ppnh
                   ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                   with "Hkh Hb") as %[Hramh0 Hramh1].
      iApply (swp_mono (run_hart_active 0)
                (fun st => ((∃ ii pr, ⌜st = Step_Pending_Interrupt (ii, pr)⌝ ∗
                               False) ∨
                            (⌜st = Step_Execute (resf,
                                zero_extend' 32
                                  (concat_vec (subrange_vec_dec w 31 16)
                                     (subrange_vec_dec w 15 0)))⌝ ∗
                             ∃ rs2 : regstate, ⌜Q rs2⌝ ∗
                             hreg_frame rs2 s_Drw ∗
                             hreg_frame_ro Df rs2 s_Dro ∗ Rr rs2))%I)
                _ with "[] [-]").
      { iIntros (st) "[Hi | (-> & Hr)]"; [ iDestruct "Hi" as (ii pr) "(_ & [])" | ].
        iExists (concat_vec (subrange_vec_dec w 31 16)
                   (subrange_vec_dec w 15 0)). by iFrame. }
      iApply (swp_run_hart_active_gen_exf_res s_Drw s_Dro Df (srs tlbv)
                Qtow Q (RtowW W) (W ∗ Res tlbv ∗ resv_frag cpu_id None)%I
                Supervisor pc
                (concat_vec (subrange_vec_dec w 31 16)
                   (subrange_vec_dec w 15 0)) i 8 Rr (fun _ _ => False%I) resf
                Hplain s_disj s_in_priv s_in_PC s_w_nPC ltac:(srs_lk)
                ltac:(intros rsf (tv & ->); srs_lk)
                ltac:(intros rsf (tv & ->);
                      rewrite concat_subranges_id;
                      exact (Hdec _ _ _ (wfi_decode_ok tv Hmisa Hmenv)))
                ltac:(intros rsf (tv & ->); exact (Hlp tv))
                with "Hcert Hrw Hro [$HW $HRes $Hfrag0] Hdisp' [] [Hex]").
      2:{ iIntros (rsf) "%HQ (HW & HRes & Hany) Hrw Hro".
          destruct HQ as (tv & ->). rewrite s_rs_tlb.
          iApply ("Hex" $! tv with "HW HRes Hany Hrw Hro"). }
      iIntros "(HW & HRes & Hany) Hrw Hro".
      iApply (spt_fetch_S_base2_P s_Drw s_Dro Df (srs tlbv) Qtow Qtow
                (RtowW W) (RtowW W) pc (pa_of ppnl pc)
                (pa_of ppnh (add_vec_int pc 2))
                (subrange_vec_dec w 15 0) (subrange_vec_dec w 31 16)
                s_disj s_in_PC s_in_misa s_in_mst s_in_priv
                ltac:(srs_lk) ltac:(intros rs1 (tv & ->); srs_lk)
                ltac:(intros rs1 (tv & ->); srs_lk)
                ltac:(intros rs2 (tv & ->); srs_lk)
                ltac:(rewrite s_rs_misa Hmisa; vm_compute; reflexivity)
                Hbit0 Hbit1 Hal HnotRVC
                with "Hcert Hrw Hro [Hany HRes HW] [] [] []").
      + iIntros "Hrw Hro". iRename "Hany" into "Hfrag".
        iApply (swp_mono with "[HW] [-]");
          [| iApply ("Htr" $! pc ppnl tlbv None with
                       "[%] [%] Hkl Hfrag HRes Hrw Hro") ].
        2:{ exact Hcanl. }
        2:{ exact Hidl. }
        iIntros (v) "(-> & Hf)". iSplitR; [done|].
        iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
        iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
        rewrite s_rs_tlb. iFrame.
      + iIntros (rs1) "%HQ Hrw Hro". destruct HQ as (tv & ->).
        iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                  (pa_of ppnl pc) pmar0 pcfg paddr
                  (subrange_vec_dec w 15 0) s_disj s_in_pma
                  s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                  ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                  HA Hord HX Hcov Hpallow Hraml0 Hraml1
                  (pa_aligned_div ppnl pc 2 ltac:(lia)
                     ltac:(exists 2048; lia) H2al)
                  with "Hcert Hrw Hro []").
        iApply (s_text_obl pc pc 0%nat 4%nat 2%N (nth_byte w) ppnl
                  (subrange_vec_dec w 15 0)
                  ltac:(lia) ltac:(lia) (fun k => eq_refl) Hoffl Hcanl
                  ltac:(intros j Hj;
                        exact (eq_sym (nth_byte_subrange_lo w j Hj)))
                  with "Hkl Hb").
      + iIntros (rs1) "%HQ (HW & HRes & Hany) Hrw Hro".
        destruct HQ as (tv & ->). rewrite s_rs_tlb.
        iDestruct "Hany" as (rr) "Hfrag".
        iApply (swp_mono with "[HW] [-]");
          [| iApply ("Htr" $! (add_vec_int pc 2) ppnh tv rr with
                       "[%] [%] Hkh Hfrag HRes Hrw Hro") ].
        2:{ exact Hcanh. }
        2:{ exact Hidh. }
        iIntros (v) "(-> & Hf)". iSplitR; [done|].
        iDestruct "Hf" as (tv') "(HRes & Hany & Hrw & Hro)".
        iExists (srs tv'). iSplitR; [iPureIntro; by exists tv' |].
        rewrite s_rs_tlb. iFrame.
      + iIntros (rs2) "%HQ Hrw Hro". destruct HQ as (tv & ->).
        iApply (swp_checked_mem_read_ifetch2_S s_Drw s_Dro Df (srs tv)
                  (pa_of ppnh (add_vec_int pc 2)) pmar0 pcfg paddr
                  (subrange_vec_dec w 31 16) s_disj s_in_pma
                  s_in_pcfg s_in_paddr s_in_htif ltac:(srs_lk)
                  ltac:(srs_lk) ltac:(srs_lk) ltac:(srs_lk)
                  HA Hord HX Hcov Hpallow Hramh0 Hramh1
                  (pa_aligned_div ppnh (add_vec_int pc 2) 2 ltac:(lia)
                     ltac:(exists 2048; lia) Hvah2)
                  with "Hcert Hrw Hro []").
        iApply (s_text_obl pc (add_vec_int pc 2) 2%nat 4%nat 2%N
                  (nth_byte w) ppnh (subrange_vec_dec w 31 16)
                  ltac:(lia) ltac:(lia) HbaseH Hoffh Hcanh
                  ltac:(intros j Hj;
                        exact (eq_sym (nth_byte_subrange_hi w j Hj)))
                  with "Hkh Hb").
  Qed.

End WfiRun.

(* ===================================================================== *)
(* THE LEAF.                                                             *)
(* ===================================================================== *)
Section WfiLeaf.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  Context {p : mword 64}.

  (* [srs] is [WpIntrInv]'s: the tower's lookups, and NOT under a [by] --
     it is used both as a closer and as a normaliser here. *)

  (* the execute datapath: at Supervisor, wfi is unconditionally a wait
     entry (no TW check here -- TW is only consulted on the FORCED-exit arm
     of [run_hart_waiting], which [riscv_step]'s pinned [exit_wait = false]
     makes unreachable). *)
  Lemma exec_execute_WFI_S (s : mstate) :
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (execute (WFI tt)) s = Some (Enter_Wait WAIT_WFI, s).
  Proof.
    intros Hpriv.
    change (execute (WFI tt)) with (execute_WFI tt).
    unfold execute_WFI.
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
    cbn beta. rewrite Hpriv. cbn match.
    apply exec_returnm.
  Qed.

  (* [execute (WFI tt)] reads cur_privilege and nothing else, so it is the
     [goodb] route: read-only, at any file whose privilege is Supervisor. *)
  Definition wfi_Db : register -> bool := fun r =>
    register_beq r (cur_privilege : register).

  Lemma wfi_Db_in (r : register) : wfi_Db r = true -> r ∈ s_Drw ∪ s_Dro.
  Proof.
    unfold wfi_Db. intros Hr. apply register_beq_eq in Hr; subst r.
    exact s_in_priv.
  Qed.

  Lemma wfi_hval_execute (rs : regstate) :
    register_lookup cur_privilege rs = Supervisor ->
    hval (s_Drw ∪ s_Dro) s_Drw rs (execute (WFI tt))
      (Enter_Wait WAIT_WFI) rs.
  Proof.
    intros Hpriv.
    apply (hval_of_goodb wfi_Db (s_Drw ∪ s_Dro) s_Drw (execute (WFI tt))
             (MState (register_set cur_privilege Supervisor init_regstate) ∅
                dev0_state) rs (Enter_Wait WAIT_WFI) wfi_Db_in).
    - intros r Hr. unfold wfi_Db in Hr. apply register_beq_eq in Hr; subst r.
      cbn [sregs]. rewrite register_lookup_set. exact Hpriv.
    - vm_compute. reflexivity.
    - apply exec_execute_WFI_S. cbn [sregs].
      rewrite register_lookup_set. reflexivity.
  Qed.

  (* THE TOWER IS OPAQUE FROM HERE.  These two lemmas are lookups BETWEEN
     two [s_rs] towers, and with the definition transparent the unifier
     answers every [exact] by unfolding 22 [register_set]s on both sides --
     8 minutes for the pair, against seconds with it sealed. *)
  #[local] Opaque s_rs.

  (* "this concrete register is in the footprint and is not one the wfi
     cycle moves" -- the side condition every [wfi_land_cell] takes. *)
  Local Ltac wfi_um :=
    apply elem_of_difference; split;
      [ rewrite /wfi_Drw /wfi_Dro; set_solver
      | rewrite /wfi_moved /tk_clock3; intros Hc;
        repeat (apply elem_of_union in Hc as [Hc|Hc]);
        apply elem_of_singleton in Hc; discriminate ].

  (* ONE CELL of the whole wfi's landing file, for the eighteen the cycle
     does not move.  Stated per register and applied at CONCRETE ones: a
     [repeat rewrite] over the S-mode tower peels through to [cold_regs]
     and does not come back (durable-notes). *)
  Lemma wfi_land_cell (r : register) (pc msr : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : mword 32)
      (micfg misa0 mseccfg0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (satp0 mdv0 : mword 64)
      (tv : type_of_register tlb) (rs2 rsP rs3 rs4 : regstate) :
    r ∈ (wfi_Drw ∪ wfi_Dro) ∖ wfi_moved ->
    register_beq r (hart_state : register) = false ->
    register_beq r (R_bitvector_64 nextPC : register) = false ->
    rs2 = register_set (R_bitvector_64 nextPC) (add_vec_int pc 4)
            (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
               mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
               MENVCFG_S tv) ->
    (exists hv, rsP = register_set hart_state hv rs2) ->
    reg_agree_on ((wfi_Drw ∪ wfi_Dro) ∖ tk_clock3) rs3 rsP ->
    wfi_wake rs3 rs4 ->
    register_lookup r rs4
    = register_lookup r
        (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
           mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
           MENVCFG_S tv).
  Proof.
    intros Hr Hhs Hnp -> (hv & ->) Hag3 (_ & _ & Hag4).
    (* NEVER [rewrite] between two register-file towers: a keyed match that
       fails on one side unfolds [register_set] and compares two update
       towers (durable-notes' 3^N bomb -- measured here at 8 MINUTES for
       this lemma and its twin).  [etransitivity] + [exact] only ever
       unifies against ONE side, so each step is constant time. *)
    etransitivity; [ exact (Hag4 r Hr) | ].
    etransitivity; [ exact (Hag3 r (wfi_unmoved_noclock r Hr)) | ].
    etransitivity;
      [ exact (irrelevant_register_set r (hart_state : register) _ _ Hhs) | ].
    exact (irrelevant_register_set r (R_bitvector_64 nextPC : register)
             _ _ Hnp).
  Qed.

  (* the PC the wfi retires at: [nextPC] survives the whole parked stretch,
     and the wake's tick copies it into PC. *)
  Lemma wfi_land_PC (pc msr : mword 64) (bmi : bool)
      (cy ti ip mst0 : mword 64) (pcfg : type_of_register pmpcfg_n)
      (paddr : type_of_register pmpaddr_n) (mc : mword 32)
      (micfg misa0 mseccfg0 : mword 64) (pmar0 : list PMA_Region)
      (elp0 : type_of_register elp) (satp0 mdv0 : mword 64)
      (tv : type_of_register tlb) (rs2 rsP rs3 rs4 : regstate) :
    rs2 = register_set (R_bitvector_64 nextPC) (add_vec_int pc 4)
            (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
               mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
               MENVCFG_S tv) ->
    (exists hv, rsP = register_set hart_state hv rs2) ->
    reg_agree_on ((wfi_Drw ∪ wfi_Dro) ∖ tk_clock3) rs3 rsP ->
    wfi_wake rs3 rs4 ->
    register_lookup (R_bitvector_64 PC) rs4 = add_vec_int pc 4
    /\ register_lookup (R_bitvector_64 nextPC) rs4 = add_vec_int pc 4
    /\ register_lookup hart_state rs4 = HART_ACTIVE tt.
  Proof.
    intros -> (hv & ->) Hag3 Hw.
    pose proof Hw as (Hh4 & Hpc4 & Hag4).
    assert (Hnp_hs : register_beq (R_bitvector_64 nextPC : register)
                       (hart_state : register) = false)
      by (apply wfi_beq_false; discriminate).
    assert (HnpcP : register_lookup (R_bitvector_64 nextPC)
              (register_set hart_state hv
                 (register_set (R_bitvector_64 nextPC) (add_vec_int pc 4)
                    (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                       misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S
                       mdv0 MENVCFG_S tv))) = add_vec_int pc 4).
    { etransitivity;
        [ exact (irrelevant_register_set (R_bitvector_64 nextPC : register)
                   (hart_state : register) _ _ Hnp_hs) | ].
      apply register_lookup_set. }
    assert (Hnp3 : register_lookup (R_bitvector_64 nextPC) rs3
                   = add_vec_int pc 4)
      by (rewrite (Hag3 _ wfi_nPC_unmoved_clock); exact HnpcP).
    split_and!.
    - rewrite Hpc4. exact Hnp3.
    - rewrite (Hag4 _ wfi_nPC_unmoved). exact Hnp3.
    - exact Hh4.
  Qed.

  (* the KPT witness rules the Bare arm out of [WpIntrInv.sie_cap_cells_at]
     only at [s_Drw], so that accessor's closer asks for [SD = s_Drwb ->
     tv' = tlbv] and the wfi has to refute the antecedent.  By NAME, not by
     [set_solver]: the leaf's context carries the S-mode towers. *)
  Lemma s_Drw_ne_Drwb : s_Drw <> s_Drwb.
  Proof.
    intros Heq. pose proof s_w_tlb as Hin. rewrite Heq /s_Drwb in Hin.
    revert Hin. clear. set_solver.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE LEAF.  [intr_count 0 false] is the caller's eighth at '0';        *)
  (* agreement with [sconf]'s mstatus-tied half pins the live SIE bit to   *)
  (* 0, which kills the ENTER step's [dispatchInterrupt Supervisor].  The  *)
  (* fetch runs through the capability's translation slot consumed FOLDED  *)
  (* as [strans_regime], so BOTH regime arms are served by one obligation. *)
  (* [sie_cap]'s arm index [b] rides through completely OPAQUE: nothing    *)
  (* here inspects it (SIE=0 comes from ghost agreement with               *)
  (* [intr_count], not from [b]), so it is threaded unchanged from premise *)
  (* to continuation with no case split -- a wfi never migrates the hart,  *)
  (* so there is no [wp_next] wrapper either.  The continuation is under a *)
  (* [▷]: the ENTER cycle's own later pays for it, which is what lets an   *)
  (* outer iLöb loop (the scheduler's head) strip its IH across the wfi.   *)
  (*                                                                      *)
  (* [kpt_on cpu_id] IS A PREMISE, and it is what keeps this leaf on ONE   *)
  (* footprint.  The wfi's ENTER step fetches, and a fetch's walk fills    *)
  (* the TLB, so [tlb] has to be in the write set -- but once              *)
  (* [SRegime.bare_inv] stops owning that cell (the kvminithart lane) a    *)
  (* Bare-arm caller cannot fund one, and serving both arms would mean a   *)
  (* second copy of the whole [wfi_Drw] footprint family.  It is not       *)
  (* needed: the kernel executes wfi in exactly one place, the scheduler,  *)
  (* which runs long after kvminithart, so the caller HAS the receipt.     *)
  (* The witness is persistent, so it costs the caller nothing to hand     *)
  (* over, and it pins the arm at KPT for the whole leaf --                *)
  (* [WpIntrInv.sie_cap_cells_at] refutes Bare from it and [tlb_res_pt]    *)
  (* funds the cell.  The arm index [b] still rides through opaque.        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_wfi_s_sconf (pc : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    kpt_on cpu_id -∗
    sie_cap_gpr kt m n b p -∗
    intr_count 0 false -∗
    pc_is pc -∗
    instr pc false (WFI tt) -∗
    ( ▷ ( sie_cap_gpr kt m n b p -∗
          intr_count 0 false -∗
          pc_is (add_vec_int pc 4) -∗
          WP (Loop : expr riscv_lang))) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hkpt Hcg Hcnt Hpc #Hinstr Hcont".
    (* ---- the bundles, into the 25 cells ---- *)
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct (sconf_to_cells with "Hsc") as (mst0 mdv0)
      "(%Hmsf & %Hmm & #Hhw & #Hminv & Hpriv & Hms & Hhalf & Htie & Hmie &
        Hmdl & Hmenv)".
    (* THE SLOT, AT THE KERNEL TABLE.  [sie_cap_to_cells] would serve, but
       it is arm-BLIND and so makes the Bare arm fund a tlb cell; the
       receipt pins the arm here instead, and the closer re-seals it. *)
    iDestruct (sie_cap_cells_at s_Drw kt m n b p (or_introl eq_refl)
                 with "[] Hcap") as (satp0 tlbv pcfg paddr)
      "(%Hsok & %Hpok & Hsatp & Htlb & Hpcfg & Hpaddr & Hres & Hrest &
        Hclose)".
    { rewrite /s_kpt_wit. iRight. iExact "Hkpt". }
    iEval (rewrite s_tlb_at_kpt) in "Htlb".
    (* SIE = 0 by ghost agreement: the tied half against the count's eighth *)
    iDestruct (ghost_var_agree with "Hhalf Hcnt") as %Hb0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE mst0) ('b"1") = false)
      by (rewrite Hb0; vm_compute; reflexivity).
    iDestruct "Hpc" as "(HPC & HnPC & Hmr & Hcr & Hresv)".
    iDestruct "Hmr" as (msr bmi mc micfg) "(Hmsr & Hmi & #Hmc & #Hmicfg)".
    iDestruct "Hcr" as (cy ti ip) "(Hcy & Hti & Hip)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmS & %HmC &
        %HmU & %HmM & %Hpmaall & %Hsec1 & %Hsec2 & %Helpnp & %HmA &
        %Hmisaval & %Hsecval & #Hkmapb)".
    iDestruct (hw_config_cert with "Hhw") as "#Hcert".
    pose proof Hmsf as Hmsf'. destruct Hmsf' as (HMPRV & HSXL & _).
    pose proof Hpok as Hpok'.
    destruct Hpok' as (HA & Hord & HX & HWp & HRp & Hcov).
    (* ---- the cycle's frame, at the tower the cells make ---- *)
    iAssert (hreg_frame (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                 MENVCFG_S tlbv) s_Drw ∗
             hreg_frame_ro (s_Df (DfracOwn 1))
               (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                  mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                  MENVCFG_S tlbv) s_Dro)%I
      with "[HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
             Hsatp Hmie Hmdl Hmenv]" as "[Hsrw Hsro]".
    { rewrite (s_frames_cells pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg
                 misa0 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                 MENVCFG_S tlbv).
      rewrite /s_cells. srs.
      iFrame "HPC HnPC Hmsr Hmi Hcy Hti Hip Htlb Hpriv Hms Hhs Hpcfg Hpaddr
              Hsatp Hmie Hmdl Hmenv".
      iFrame "Hmc Hmicfg Hmisa Hmseccfg Hpma Hhtif Help Hsenv". }
    iCombine "Hsrw Hsro" as "Hsf".
    iEval (rewrite -wfi_frames_s) in "Hsf".
    iDestruct "Hsf" as "[Hrw Hro]".
    (* ---- THE ENTER CYCLE ---- *)
    iApply (swp_exec_step_full wfi_Drw wfi_Dro (s_Df (DfracOwn 1))
              (s_rs pc pc msr bmi cy ti ip mst0 pcfg paddr mc micfg misa0
                 mseccfg0 (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                 MENVCFG_S tlbv)
              (s_rs pc pc msr (minstret_inc_flag mc micfg Supervisor) cy ti ip
                 mst0 pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0)
                 pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S tlbv)
              (fun st rs2 =>
                 (exists w0 : SailStdpp.Values.mword 32,
                    st = Step_Execute (Enter_Wait WAIT_WFI,
                                       zero_extend' 32 w0)) /\
                 (exists tv : type_of_register tlb,
                    rs2 = register_set (R_bitvector_64 nextPC)
                            (add_vec_int pc 4)
                            (s_rs pc pc msr
                               (minstret_inc_flag mc micfg Supervisor) cy ti
                               ip mst0 pcfg paddr mc micfg misa0 mseccfg0
                               (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                               MENVCFG_S tv)))
              (fun rs2 => (gpr_file (tp_pin m) ∗ intr_count 0 false ∗
                 ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗
                 sret_tie mst0 ∗ sie_cap_rest kt m n b p ∗
                 strans_res_at satp0 (register_lookup tlb rs2) ∗
                 resv_any cpu_id)%I)
              wfi_disj wfi_w_cy wfi_w_ti wfi_w_ip wfi_in_priv wfi_w_hart
              wfi_in_hart wfi_in_mc wfi_in_micfg wfi_w_mi wfi_in_mi wfi_w_ms
              wfi_in_ms wfi_w_PC wfi_in_PC wfi_in_nPC
              ltac:(by srs)
              ltac:(intros st rs2 (_ & (tv & ->));
                    etransitivity;
                      [ exact (irrelevant_register_set
                                 (hart_state : register)
                                 (R_bitvector_64 nextPC : register) _ _
                                 eq_refl) | ];
                    by srs)
              ltac:(intros st rs2 (_ & (tv & ->));
                    etransitivity;
                      [ exact (irrelevant_register_set
                                 (R_bool minstret_increment : register)
                                 (R_bitvector_64 nextPC : register) _ _
                                 eq_refl) | ];
                    by srs)
              ltac:(rewrite wfi_union;
                    exact (s_pre_agree pc msr bmi cy ti ip mst0 pcfg paddr mc
                             micfg misa0 mseccfg0 (mword_of_int 0) pmar0 elp0
                             satp0 MIE_S mdv0 MENVCFG_S tlbv))
              with "Hcert Hresv Hrw Hro [Hfile Hcnt Hhalf Htie Hrest Hres]
                    [Hcont Hclose]").
    - (* ---------------- THE ENTER STEP'S BODY ---------------- *)
      iIntros "Hfrag Hrw Hro".
      iCombine "Hrw Hro" as "Hf". iEval (rewrite wfi_frames_s) in "Hf".
      iDestruct "Hf" as "[Hrw Hro]".
      iApply (swp_mono with "[] [-]").
      2:{ iApply (wfi_run_enter (s_Df (DfracOwn 1)) pc msr
                    (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                    pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0
                    elp0 satp0 MIE_S mdv0 MENVCFG_S
                    (strans_res_at satp0) tlbv (WFI tt)
                    (Enter_Wait WAIT_WFI)
                    (fun rs2 => exists tv : type_of_register tlb,
                       rs2 = register_set (R_bitvector_64 nextPC)
                               (add_vec_int pc 4)
                               (s_rs pc pc msr
                                  (minstret_inc_flag mc micfg Supervisor) cy
                                  ti ip mst0 pcfg paddr mc micfg misa0
                                  mseccfg0 (mword_of_int 0) pmar0 elp0 satp0
                                  MIE_S mdv0 MENVCFG_S tv))
                    (fun rs2 => (gpr_file (tp_pin m) ∗ intr_count 0 false ∗
                       ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗
                       sret_tie mst0 ∗ sie_cap_rest kt m n b p ∗
                       strans_res_at satp0 (register_lookup tlb rs2) ∗
                       resv_any cpu_id)%I)
                    (gpr_file (tp_pin m) ∗ intr_count 0 false ∗
                     ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗
                     sret_tie mst0 ∗ sie_cap_rest kt m n b p)%I
                    eq_refl Hmisaval eq_refl Helpnp HSIE Hmm
                    (pma_all_ram Hpmaall) HA Hord HX Hcov
                    with "Hcert Hinstr [$Hfile $Hcnt $Hhalf $Htie $Hrest]
                          Hfrag Hres Hrw Hro [] []").
      - (* the fetch translation, from the regime's own swp face *)
        iApply (spt_tr_obl_of_regime strans_regime (s_Df (DfracOwn 1)) i_Db
                  pc msr (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                  pcfg paddr mc micfg misa0 mseccfg0 (mword_of_int 0) pmar0
                  elp0 satp0 MIE_S mdv0 MENVCFG_S
                  Hmisaval eq_refl HSXL HMPRV i_Db_in
                  ltac:(intros r Hr; unfold D_leafchk in Hr;
                        apply orb_true_elim in Hr as [Hr | Hr];
                        apply register_beq_eq in Hr; subst r;
                        [exact s_in_misa | exact s_in_menv])
                  ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity)
                  Hsok Hpok (pma_all_ram Hpmaall) with "Hcert").
      - (* the execute: wfi enters the WAIT state, and writes nothing *)
        iIntros (tv') "HW HRes Hany Hrw Hro".
        (* the privilege at the fetch's landing file, POSED: an [ltac:] in
           argument position runs while the file is still an evar. *)
        assert (Hpriv_f : register_lookup cur_privilege
                  (register_set (R_bitvector_64 nextPC) (add_vec_int pc 4)
                     (s_rs pc pc msr (minstret_inc_flag mc micfg Supervisor)
                        cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
                        (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                        MENVCFG_S tv')) = Supervisor).
        { etransitivity;
            [ exact (irrelevant_register_set (cur_privilege : register)
                       (R_bitvector_64 nextPC : register) _ _ eq_refl) | ].
          apply s_rs_priv. }
        iApply (swp_mono with "[HW HRes Hany] [Hrw Hro]").
        2:{ iApply (swp_span s_Drw s_Dro (s_Df (DfracOwn 1))
                      (register_set (R_bitvector_64 nextPC)
                         (add_vec_int pc 4)
                         (s_rs pc pc msr
                            (minstret_inc_flag mc micfg Supervisor) cy ti ip
                            mst0 pcfg paddr mc micfg misa0 mseccfg0
                            (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0
                            MENVCFG_S tv'))
                      _ _ _ s_disj (wfi_hval_execute _ Hpriv_f)
                      with "Hcert Hrw Hro"). }
        iIntros (e) "(-> & Hrw & Hro)". iSplitR; [done|].
        iExists (register_set (R_bitvector_64 nextPC) (add_vec_int pc 4)
                   (s_rs pc pc msr (minstret_inc_flag mc micfg Supervisor) cy
                      ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0
                      (mword_of_int 0) pmar0 elp0 satp0 MIE_S mdv0 MENVCFG_S
                      tv')).
        iSplitR; [ iPureIntro; by exists tv' | ].
        iEval (rewrite (irrelevant_register_set (tlb : register)
                          (R_bitvector_64 nextPC : register) _ _ eq_refl)
               s_rs_tlb).
        iFrame. }
      (* the post: the Step pins the arm, the frames go back to wfi *)
      iIntros (st) "H". iDestruct "H" as (w0) "(-> & Hr)".
      iDestruct "Hr" as (rs2) "(%HQ & Hrw & Hro & HR)".
      iExists rs2. iSplitR.
      { iPureIntro. split; [ by exists w0 | exact HQ ]. }
      cbn [tsf_post]. iSplitR; [done|].
      iCombine "Hrw Hro" as "Hf". iEval (rewrite -wfi_frames_s) in "Hf".
      iDestruct "Hf" as "[$ $]". iExact "HR".
    - (* ---------------- THE WAIT PHASE AND THE WAKE ---------------- *)
      iNext. iIntros (rs3 rs2) "%Hpost Hrw Hro HPsi".
      destruct Hpost as (rsP & Htsf & Hag3).
      destruct Htsf as (st & (Hst & (tv & Hrs2)) & Hlast).
      destruct Hst as (w0 & ->). cbn [tsf_post] in Hlast.
      destruct Hlast as (_ & HrsP).
      iDestruct "HPsi" as "(Hfile & Hcnt & Hhalf & Htie & Hrest & HRes & Hany)".
      assert (Hhart3 : register_lookup hart_state rs3
                       = HART_WAITING (WAIT_WFI, zero_extend' 32 w0)).
      { etransitivity; [ exact (Hag3 _ wfi_hart_noclock) | ].
        rewrite HrsP. apply register_lookup_set. }
      iApply (wfi_wait_loop (zero_extend' 32 w0)
                (gpr_file (tp_pin m) ∗ intr_count 0 false ∗
                 ghost_var sie_gname (1/2) (_get_Mstatus_SIE mst0) ∗
                 sret_tie mst0 ∗ sie_cap_rest kt m n b p ∗
                 strans_res_at satp0 (register_lookup tlb rs2))%I
                rs3 Hhart3
                with "Hcert Hany Hrw Hro [$Hfile $Hcnt $Hhalf $Htie $Hrest $HRes]
                      [Hcont Hclose]").
      iIntros (rs4) "%Hwake Hrw Hro Hany
                     (Hfile & Hcnt & Hhalf & Htie & Hrest & HRes)".
      (* ---- the landing tower, cell by cell ---- *)
      pose proof (wfi_land_PC pc msr (minstret_inc_flag mc micfg Supervisor)
                    cy ti ip mst0 pcfg paddr mc micfg misa0 mseccfg0 pmar0
                    elp0 satp0 mdv0 tv rs2 rsP rs3 rs4 Hrs2
                    (ex_intro _ _ HrsP) Hag3 Hwake) as (Hpc4 & Hnp4 & Hh4).
      pose proof (fun (r : register) Hr Hhs Hnp =>
                    wfi_land_cell r pc msr
                      (minstret_inc_flag mc micfg Supervisor) cy ti ip mst0
                      pcfg paddr mc micfg misa0 mseccfg0 pmar0 elp0 satp0
                      mdv0 tv rs2 rsP rs3 rs4 Hr Hhs Hnp Hrs2
                      (ex_intro _ _ HrsP) Hag3 Hwake) as Hcell.
      iCombine "Hrw Hro" as "Hf". iEval (rewrite wfi_rw_split wfi_ro_split)
        in "Hf".
      iDestruct "Hf" as "((HPC & HnPC & Hmsr & Hmi & Hcy & Hti & Hip & Htlb &
                          Hhs) &
                         (Hpriv & Hms & Hpcfg & Hpaddr & _ & _ & _ & _ & _ &
                          _ & _ & _ & Hsatp & Hmie & Hmdl & Hmenv))".
      rewrite Hpc4 Hnp4 Hh4.
      rewrite (Hcell (tlb : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_tlb.
      rewrite (Hcell (cur_privilege : register) ltac:(wfi_um)
                 ltac:(reflexivity) ltac:(reflexivity)) s_rs_priv.
      rewrite (Hcell (mstatus : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_mst.
      rewrite (Hcell (pmpcfg_n : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_pcfg.
      rewrite (Hcell (pmpaddr_n : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_paddr.
      rewrite (Hcell (satp : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_satp.
      rewrite (Hcell (mie : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_mie.
      rewrite (Hcell (mideleg : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_mdl.
      rewrite (Hcell (menvcfg : register) ltac:(wfi_um) ltac:(reflexivity)
                 ltac:(reflexivity)) s_rs_menv.
      (* ---- and the bundles back ---- *)
      iApply ("Hcont" with "[Hhs Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv Hsatp
                             Htlb Hpcfg Hpaddr HRes Hrest Hfile Hclose] Hcnt
                            [HPC HnPC Hmsr Hmi Hcy Hti Hip Hany]").
      + iApply (sie_cap_gpr_join with "Hhs [Hpriv Hms Hhalf Htie Hmie Hmdl
                                            Hmenv] [Hsatp Htlb Hpcfg Hpaddr
                                            HRes Hrest Hclose] Hfile").
        * iApply (sconf_of_cells mst0 mdv0 Hmsf Hmm
                    with "Hhw Hminv Hpriv Hms Hhalf Htie Hmie Hmdl Hmenv").
        * iAssert (s_tlb_at s_Drw tv) with "[Htlb]" as "Htlb".
          { rewrite s_tlb_at_kpt. iExact "Htlb". }
          iApply ("Hclose" $! m n b tv
                    with "[%] Hsatp Htlb Hpcfg Hpaddr [HRes] Hrest").
          { intros Hbad. exfalso. exact (s_Drw_ne_Drwb Hbad). }
          rewrite Hrs2.
          iEval (rewrite (irrelevant_register_set (tlb : register)
                            (R_bitvector_64 nextPC : register) _ _ eq_refl)
                 s_rs_tlb) in "HRes". iExact "HRes".
      + rewrite /pc_is. iFrame "HPC HnPC Hany".
        iSplitL "Hmsr Hmi".
        { iExists (register_lookup (R_bitvector_64 minstret) rs4),
                  (register_lookup (R_bool minstret_increment) rs4), mc, micfg.
          iFrame "Hmsr Hmi Hmc Hmicfg". }
        iExists (register_lookup (R_bitvector_64 mcycle) rs4),
                (register_lookup (R_bitvector_64 mtime) rs4),
                (register_lookup (R_bitvector_64 mip) rs4).
        iFrame "Hcy Hti Hip".
  Qed.

End WfiLeaf.
