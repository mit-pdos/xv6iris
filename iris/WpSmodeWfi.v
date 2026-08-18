(* WpSmodeWfi.v -- the [wfi] instruction leaf at the sconf tier.

   [wfi] is the only instruction in the kernel whose model semantics is
   NOT one retiring machine step, so it cannot go through the
   [wp_instr_s_sconf] funnel (whose σ-callback shape assumes a retiring
   instruction).  The model:

     - [execute_WFI tt] at Supervisor returns [Enter_Wait WAIT_WFI];
       since [wait_is_nop WAIT_WFI = false], [try_step]'s postlude writes
       [hart_state := HART_WAITING (WAIT_WFI, instbits)] and -- the hart
       now being WAITING -- performs NEITHER [tick_pc] NOR the minstret
       bump.  So after the ENTER step PC still points at the wfi and the
       nextPC = pc+4 written by the fetch/execute bookkeeping survives.
     - every later step goes through [run_hart_waiting], which reads
       [shouldWakeForInterrupt] = [mip & mie <> 0] straight off σ (mip
       lives in [clock_inv], so the branch is demonic and needs no
       ownership at all):
         * no wake: [exit_wait] is pinned [false] by [riscv_step], so the
           (WAIT_WFI, _, true) arm -- the only one that reads mstatus.TW --
           is DEAD, and the match falls to [(_, _, false)] -> [Step_Waiting];
           the postlude sees HART_WAITING and returns.  The ONLY state
           change of a stutter step is the [minstret_increment] rewrite at
           the top of [try_step].
         * wake: [hart_state := HART_ACTIVE], [Retire_Success]; the
           postlude runs [tick_pc] (PC := nextPC = pc+4) and the minstret
           bump.

   So the leaf is: one bespoke ENTER step on the raw [wp_exec_step_minstret]
   tier (fetch driven through the caller's [sie_cap] translation slot, as an
   SIE=0 data leaf does, via [s_regime_fetch strans_regime]; the enter step
   goes through [run_hart_active], so [dispatchInterrupt Supervisor] is
   discharged to [None] from ghost-derived SIE=0), followed by an iLöb loop
   over the WAITING state which holds the [hart_state] cell itself and cases
   on [shouldWakeForInterrupt] at every step.  The stutter's later feeds the
   iLöb IH; the wake step's later feeds the caller's ▷-continuation --
   partial correctness makes "waits forever" perfectly fine. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile HartTp WpGpr MinstretInv InstrBytes.
Require Import SmodeCore SmodeCorePt.
Require Import SRegime.   (* sr_ktier_wit_KT0: the fetch engine's tier witness *)
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The pure exec layer: the three [riscv_step] shapes of a wfi.        *)
(* ===================================================================== *)

(* The execute datapath: at Supervisor, wfi is unconditionally a wait
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
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
  rewrite Hpriv. cbn match.
  apply exec_returnm.
Qed.

(* ---- the ENTER step: run_hart_active yields [Enter_Wait wr] (a
   non-nop wait), so the postlude parks the hart and does NOT tick PC or
   bump minstret. ---- *)
Section StepEnterWait.
  Context (s s_exec : mstate) (retval : mword 32) (b : bool) (wr : WaitReason).

  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Hypothesis Hhart_a :
    register_lookup hart_state
      (set_reg s (R_bool minstret_increment) b).(sregs) = HART_ACTIVE tt.
  Hypothesis Hha :
    exec (run_hart_active 0) (set_reg s (R_bool minstret_increment) b)
      = Some (Step_Execute (Enter_Wait wr, retval), s_exec).
  Hypothesis Hnop : wait_is_nop wr = false.

  Lemma exec_riscv_step_enter_wait :
    exec (riscv_step false) s
      = Some (tt, set_reg s_exec hart_state (HART_WAITING (wr, retval))).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s
                   = Some (true, set_reg s_exec hart_state (HART_WAITING (wr, retval))))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_read_reg hart_state (set_reg s (R_bool minstret_increment) b))).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hha). cbn beta iota.
    (* the Enter_Wait arm: park the hart, then the postlude's hart_state read *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ rewrite Hnop. cbn match.
            unfold get_config_print_instr. cbn match.
            erewrite exec_bind0_Some. 2:{ apply exec_returnm. }
            apply exec_write_reg. }
        apply exec_read_reg. }
    rewrite register_lookup_set. cbn beta iota.
    apply exec_returnm.
  Qed.
End StepEnterWait.

(* ---- a WAITING step: shouldWakeForInterrupt reads mip & mie off the
   state; both outcomes are register-only computations. ---- *)
Lemma exec_shouldWakeForInterrupt (s : mstate) :
  exec (shouldWakeForInterrupt tt) s
    = Some (neq_vec (and_vec (register_lookup mip s.(sregs))
                             (register_lookup mie s.(sregs))) (zeros' 64), s).
Proof.
  unfold shouldWakeForInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mip s)). cbn beta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)). cbn beta.
  apply exec_returnm.
Qed.

(* the STUTTER: no wake, [exit_wait = false] -- the [(_, _, false)] arm. *)
Section StepWaitStutter.
  Context (s : mstate) (instbits : mword 32) (b : bool).

  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Hypothesis Hhart_a :
    register_lookup hart_state (set_reg s (R_bool minstret_increment) b).(sregs)
      = HART_WAITING (WAIT_WFI, instbits).
  Hypothesis Hnowake :
    neq_vec (and_vec (register_lookup mip
                        (set_reg s (R_bool minstret_increment) b).(sregs))
                     (register_lookup mie
                        (set_reg s (R_bool minstret_increment) b).(sregs)))
            (zeros' 64) = false.

  Lemma exec_riscv_step_wait_stutter :
    exec (riscv_step false) s = Some (tt, set_reg s (R_bool minstret_increment) b).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s
                   = Some (true, set_reg s (R_bool minstret_increment) b))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_read_reg hart_state (set_reg s (R_bool minstret_increment) b))).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    (* run_hart_waiting: no wake -> Step_Waiting *)
    erewrite exec_bind_Some.
    2:{ unfold run_hart_waiting.
        rewrite (exec_bind_Some _ _ _ _ _
                  (exec_shouldWakeForInterrupt
                     (set_reg s (R_bool minstret_increment) b))).
        rewrite Hnowake. cbn beta iota.
        destruct (valid_reservation tt); cbn beta iota;
          (unfold get_config_print_instr; cbn match;
           erewrite exec_bind0_Some; [| apply exec_returnm ];
           apply exec_returnm). }
    cbn beta iota.
    (* postlude: Step_Waiting -> assert hart_is_waiting -> read hart_state *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some. 2:{ apply exec_read_reg. }
            rewrite Hhart_a. unfold Defs.assert_exp. cbn [hart_is_waiting].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart_a. cbn beta iota.
    apply exec_returnm.
  Qed.
End StepWaitStutter.

(* the wake / stutter reductions of [run_hart_waiting] itself, factored out
   so the try_step wrapper below never has to see them. *)
Lemma exec_run_hart_waiting_wake (s : mstate) (instbits : mword 32) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = true ->
  exec (run_hart_waiting 0 WAIT_WFI instbits false) s
    = Some (Step_Execute (RETIRE_SUCCESS, instbits),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hwake.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)).
  rewrite Hwake. cbn beta iota.
  unfold get_config_print_instr. cbn match.
  erewrite exec_bind0_Some. 2:{ apply exec_returnm. }
  apply exec_returnm.
Qed.

(* the WAKE step: mip & mie <> 0 -- the hart is re-activated and the parked
   instruction RETIRES, so the postlude ticks PC (:= nextPC, still the wfi's
   pc+4) and bumps minstret.  Structurally the [exec_riscv_step_hart_active]
   wrapper with the hart_state read landing in the WAITING arm. *)
Section StepWaitRetire.
  Context (s s_exec : mstate) (retval instbits : mword 32) (b : bool)
          (npc mst : mword 64).

  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Hypothesis Hhart_a :
    register_lookup hart_state (set_reg s (R_bool minstret_increment) b).(sregs)
      = HART_WAITING (WAIT_WFI, instbits).
  Hypothesis Hhw :
    exec (run_hart_waiting 0 WAIT_WFI instbits false)
         (set_reg s (R_bool minstret_increment) b)
      = Some (Step_Execute (RETIRE_SUCCESS, retval), s_exec).
  Hypothesis Hhart_exec : register_lookup hart_state s_exec.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_exec :
    register_lookup (R_bool minstret_increment) s_exec.(sregs) = b.
  Hypothesis Hnpc : register_lookup nextPC s_exec.(sregs) = npc.
  Hypothesis Hmst : register_lookup minstret s_exec.(sregs) = mst.

  Lemma exec_riscv_step_wait_retire :
    exec (riscv_step false) s
      = Some (tt, if b then set_reg (set_reg s_exec PC npc) minstret
                              (add_vec_int mst 1)
                  else set_reg s_exec PC npc).
  Proof using All.
    assert (Hmst_tick :
      register_lookup minstret (set_reg s_exec PC npc).(sregs) = mst).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hmst | reflexivity ]. }
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s
                   = Some (false, if b then set_reg (set_reg s_exec PC npc) minstret
                                            (add_vec_int mst 1)
                                  else set_reg s_exec PC npc))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _
              (exec_read_reg hart_state (set_reg s (R_bool minstret_increment) b))).
    cbn beta. rewrite Hhart_a. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hhw). cbn beta.
    unfold RETIRE_SUCCESS. cbn beta iota.
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_exec. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart_exec. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ rewrite exec_tick_pc. rewrite Hnpc. reflexivity. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    change (get_config_rvfi tt) with false.
    replace (register_lookup minstret_increment (set_reg s_exec PC npc).(sregs))
      with b.
    2:{ rewrite ?sregs_set_reg.
        rewrite irrelevant_register_set;
          [ (exact Hmi_exec || (symmetry; exact Hmi_exec)) | reflexivity ]. }
    destruct b.
    - rewrite <- Hmst_tick.
      erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ erewrite exec_bind_Some.
              2:{ apply (exec_read_reg minstret). }
              apply exec_write_reg. }
          cbn beta iota. reflexivity. }
      reflexivity.
    - erewrite exec_bind0_Some.
      2:{ erewrite exec_bind0_Some.
          2:{ cbn beta iota. reflexivity. }
          cbn beta iota. reflexivity. }
      reflexivity.
  Qed.
End StepWaitRetire.

(* ---- σ-level wrappers.  [minstret_increment] is distinct from every
   register the three step shapes read, so all the pure side conditions can
   be read straight off the PRE-step state -- which is exactly the state the
   Iris layer owns cells against. ---- *)

Lemma exec_riscv_step_wfi_enter (s s_exec : mstate) (retval : mword 32) (b : bool) :
  exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s = Some (b, s) ->
  register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
  exec (run_hart_active 0) (set_reg s (R_bool minstret_increment) b)
    = Some (Step_Execute (Enter_Wait WAIT_WFI, retval), s_exec) ->
  exec (riscv_step false) s
    = Some (tt, set_reg s_exec hart_state (HART_WAITING (WAIT_WFI, retval))).
Proof.
  intros Hsi Lhs Hha.
  assert (Hhart_a : register_lookup hart_state
                      (set_reg s (R_bool minstret_increment) b).(sregs)
                    = HART_ACTIVE tt).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [ exact Lhs | reflexivity ]. }
  exact (exec_riscv_step_enter_wait s s_exec retval b WAIT_WFI Hsi Hhart_a Hha eq_refl).
Qed.

Lemma exec_riscv_step_wfi_stutter (s : mstate) (instbits : mword 32) (b : bool) :
  exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s = Some (b, s) ->
  register_lookup hart_state s.(sregs) = HART_WAITING (WAIT_WFI, instbits) ->
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = false ->
  exec (riscv_step false) s = Some (tt, set_reg s (R_bool minstret_increment) b).
Proof.
  intros Hsi Lhs Hnw.
  assert (Hhart_a : register_lookup hart_state
                      (set_reg s (R_bool minstret_increment) b).(sregs)
                    = HART_WAITING (WAIT_WFI, instbits)).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [ exact Lhs | reflexivity ]. }
  assert (Hnw' : neq_vec (and_vec (register_lookup mip
                                    (set_reg s (R_bool minstret_increment) b).(sregs))
                                  (register_lookup mie
                                    (set_reg s (R_bool minstret_increment) b).(sregs)))
                         (zeros' 64) = false).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [| reflexivity ].
    rewrite irrelevant_register_set; [| reflexivity ].
    exact Hnw. }
  exact (exec_riscv_step_wait_stutter s instbits b Hsi Hhart_a Hnw').
Qed.

Lemma exec_riscv_step_wfi_wake (s : mstate) (instbits : mword 32) (b : bool)
    (npc mst : mword 64) :
  exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s = Some (b, s) ->
  register_lookup hart_state s.(sregs) = HART_WAITING (WAIT_WFI, instbits) ->
  register_lookup nextPC s.(sregs) = npc ->
  register_lookup minstret s.(sregs) = mst ->
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = true ->
  exec (riscv_step false) s
    = Some (tt,
            if b
            then set_reg (set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                                     hart_state (HART_ACTIVE tt)) PC npc)
                         minstret (add_vec_int mst 1)
            else set_reg (set_reg (set_reg s (R_bool minstret_increment) b)
                            hart_state (HART_ACTIVE tt)) PC npc).
Proof.
  intros Hsi Lhs Lnpc Lmst Hw.
  assert (Hhart_a : register_lookup hart_state
                      (set_reg s (R_bool minstret_increment) b).(sregs)
                    = HART_WAITING (WAIT_WFI, instbits)).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [ exact Lhs | reflexivity ]. }
  assert (Hw' : neq_vec (and_vec (register_lookup mip
                                   (set_reg s (R_bool minstret_increment) b).(sregs))
                                 (register_lookup mie
                                   (set_reg s (R_bool minstret_increment) b).(sregs)))
                        (zeros' 64) = true).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [| reflexivity ].
    rewrite irrelevant_register_set; [| reflexivity ].
    exact Hw. }
  pose proof (exec_run_hart_waiting_wake
                (set_reg s (R_bool minstret_increment) b) instbits Hw') as Hhw.
  assert (Hhart_e : register_lookup hart_state
                      (set_reg (set_reg s (R_bool minstret_increment) b)
                         hart_state (HART_ACTIVE tt)).(sregs) = HART_ACTIVE tt)
    by apply register_lookup_set.
  assert (Hmi_e : register_lookup (R_bool minstret_increment)
                    (set_reg (set_reg s (R_bool minstret_increment) b)
                       hart_state (HART_ACTIVE tt)).(sregs) = b).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [| reflexivity ].
    apply register_lookup_set. }
  assert (Hnpc_e : register_lookup nextPC
                     (set_reg (set_reg s (R_bool minstret_increment) b)
                        hart_state (HART_ACTIVE tt)).(sregs) = npc).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [| reflexivity ].
    rewrite irrelevant_register_set; [| reflexivity ].
    exact Lnpc. }
  assert (Hmst_e : register_lookup minstret
                     (set_reg (set_reg s (R_bool minstret_increment) b)
                        hart_state (HART_ACTIVE tt)).(sregs) = mst).
  { rewrite ?sregs_set_reg.
    rewrite irrelevant_register_set; [| reflexivity ].
    rewrite irrelevant_register_set; [| reflexivity ].
    exact Lmst. }
  exact (exec_riscv_step_wait_retire s _ instbits instbits b npc mst
           Hsi Hhart_a Hhw Hhart_e Hmi_e Hnpc_e Hmst_e).
Qed.

(* ===================================================================== *)
(* §2 The Iris layer.                                                     *)
(* ===================================================================== *)
Section WpSmodeWfi.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ------------------------------------------------------------------- *)
  (* THE WAIT PHASE.  At this tier the caller owns the [hart_state] cell   *)
  (* across the step (the hart-active engines hold it for their client;    *)
  (* here it is the thing that CHANGES, twice), plus the PC / nextPC cells *)
  (* out of lock-step: PC is still the wfi's pc while nextPC already holds *)
  (* pc+4, and nothing in the wait phase writes either (a stutter rewrites *)
  (* only [minstret_increment]; the clock tick touches only mcycle / mtime *)
  (* / mip, which [wp_exec_step_minstret] absorbs one layer down).         *)
  (* Everything the client is owed rides through as the opaque [R].        *)
  (* The loop is a Löb induction whose IH is stripped by the STUTTER       *)
  (* step's own later; the WAKE step's later is spent on the continuation. *)
  (* Partial correctness makes "never wakes" a perfectly good outcome.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_wfi_wait (pc : mword 64) (instbits : mword 32)
      (R : iProp Σ) :
    minstret_inv -∗
    hart_state ↦ᵣ HART_WAITING (WAIT_WFI, instbits) -∗
    PC ↦ᵣ pc -∗
    nextPC ↦ᵣ (add_vec_int pc 4) -∗
    R -∗
    ( hart_state ↦ᵣ HART_ACTIVE tt -∗
      pc_is (add_vec_int pc 4) -∗
      R -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hminv Hhs Hpcr Hnpc HR Hcont".
    iRevert "Hhs Hpcr Hnpc HR Hcont".
    iLöb as "IH".
    iIntros "Hhs Hpcr Hnpc HR Hcont".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) with "Hminv").
    iIntros (σ) "[Hreg Hmem] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid with "Hreg Hhs")  as %Lhs.
    iDestruct (reg_valid with "Hreg Hpcr") as %Lpc.
    iDestruct (reg_valid with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid with "Hreg Hmst") as %Lmst.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    destruct (neq_vec (and_vec (register_lookup mip σ.(sregs))
                               (register_lookup mie σ.(sregs))) (zeros' 64)) eqn:Hw.
    - (* ---- WAKE: hart re-activated, the parked wfi retires at pc+4 ---- *)
      iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
      iMod (reg_update _ PC _ (add_vec_int pc 4) with "Hreg Hpcr") as "[Hreg Hpcr]".
      iDestruct ("Hcont" with "Hhs [$Hpcr $Hnpc] HR") as "HWP".
      iModIntro.
      iExists (if b
               then set_reg (set_reg (set_reg (set_reg σ (R_bool minstret_increment) b)
                                        hart_state (HART_ACTIVE tt)) PC (add_vec_int pc 4))
                            minstret (add_vec_int mst 1)
               else set_reg (set_reg (set_reg σ (R_bool minstret_increment) b)
                               hart_state (HART_ACTIVE tt)) PC (add_vec_int pc 4)).
      iSplitR.
      { iPureIntro.
        exact (exec_riscv_step_wfi_wake σ instbits b (add_vec_int pc 4) mst
                 Hsi Lhs Lnpc Lmst Hw). }
      iNext.
      destruct b.
      + iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst")
          as "[Hreg Hmst]".
        iModIntro. rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg.
        iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
        iExact "HWP".
      + iModIntro. rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg.
        iFrame "Hreg Hmem".
        iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
        iExact "HWP".
    - (* ---- STUTTER: only [minstret_increment] is rewritten ---- *)
      iModIntro.
      iExists (set_reg σ (R_bool minstret_increment) b).
      iSplitR.
      { iPureIntro. exact (exec_riscv_step_wfi_stutter σ instbits b Hsi Lhs Hw). }
      iNext. iModIntro.
      rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg.
      iFrame "Hreg Hmem".
      iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
      iApply ("IH" with "Hhs Hpcr Hnpc HR Hcont").
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE LEAF.  [intr_count 0 false] is the caller's eighth at '0';        *)
  (* agreement with [sconf]'s mstatus-tied half pins the live SIE bit to   *)
  (* 0, which (with [mie & ~mideleg = 0] out of [sconf]) kills the ENTER    *)
  (* step's [dispatchInterrupt Supervisor].  The fetch is driven through   *)
  (* the caller's [sie_cap] translation slot, consumed FOLDED as           *)
  (* [strans_regime] -- so BOTH regime arms (Bare and kernel-PT) are       *)
  (* served by the one [s_regime_fetch] call, with no skolem-root          *)
  (* open/repack.  [sie_cap]'s arm index [b] rides through completely      *)
  (* OPAQUE: nothing here inspects it (the SIE=0 fact comes from ghost      *)
  (* agreement with [intr_count], not from [b]), so it is threaded          *)
  (* unchanged from premise to continuation with no case split -- a wfi     *)
  (* never migrates the hart, so there is no [wp_next] wrapper either.      *)
  (* The continuation is under a [▷]: the WAKE step's own                  *)
  (* later pays for it, which is what lets an outer iLöb loop (scheduler's *)
  (* 0x1e00 head) strip its IH across the wfi.                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_wfi_s_sconf (pc : mword 64)
      (m : regfile) (n : nat) (b : bool) :
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
    iIntros "Hcg Hcnt Hpc Hinstr Hcont".
    iDestruct (sie_cap_gpr_split with "Hcg") as "(Hhs & Hsc & Hcap & Hfile)".
    iDestruct "Hcap" as "(Hstk & Htr & Harm & #Hwit)".
    iDestruct "Hsc" as "(#Hhw & #Hminv & Hpriv & Hmsx & Hmiex & Hmenvx)".
    iDestruct "Hmsx" as (ms) "(Hms & Hhalf & Hspp & %Hmsf)".
    pose proof Hmsf as Hmsf'.
    destruct Hmsf' as (HMPRV & HSXL & HMXR & HTSR & HXS & HFS & HVS & HSD & HMPP & HTVM).
    (* SIE = 0 by ghost agreement: the tied half vs the count's eighth *)
    iDestruct (ghost_var_agree with "Hhalf Hcnt") as %Hb0.
    assert (HSIE : eq_vec (_get_Mstatus_SIE ms) ('b"1") = false)
      by (rewrite Hb0; vm_compute; reflexivity).
    (* [mie] is PINNED at [MIE_S] by [sconf], so only [mideleg] is bound
       here and [Hmm] is already the fact at the literal cause set. *)
    iDestruct "Hmiex" as (mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvx" as (menvcfg0)
      "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom & %Hmenvval0)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & #Hsenv & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA & %Hmisa_val0 & %Hmseccfg_val0 & #Hkmapb)".
    iDestruct "Hinstr" as "[%Hnlpad Hr]".
    iDestruct "Hr" as (r) "[%Hrvc [Hbytes Hdec]]".
    iAssert (⌜ match r with F_Base _ => True | F_RVC _ => True | _ => False end ⌝)%I as %Hrok.
    { iEval (rewrite /instr_bytes) in "Hbytes".
      iDestruct "Hbytes" as "[_ Hb]".
      destruct r; [iDestruct "Hb" as %[] | done | done | iDestruct "Hb" as %[] ]. }
    destruct r as [e | w | h | erx]; [ done | | cbn [fetch_is_rvc] in Hrvc; discriminate | done ].
    iDestruct "Hpc" as "[Hpcr Hnpc]".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) with "Hminv").
    iIntros (σ) "Hsi Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid with "Hreg Hhs") as %Lhs0.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [mib Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ mib with "Hreg Hmi") as "[Hreg Hmi]".
    iAssert (mstate_interp (set_reg σ (R_bool minstret_increment) mib))
      with "[Hreg Hmem]" as "Hsi".
    { rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    set (σa := set_reg σ (R_bool minstret_increment) mib).
    (* the ENTER step goes through run_hart_active: dispatch must be None *)
    iDestruct (dispatchInterrupt_none_S_from_regs σa misa0 ms MIE_S mdv0
                 HmisaS Hmm HSIE with "Hsi Hmisa Hms Hmie Hmdl") as %Hdisp.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpcr")  as %Lpc.
    iDestruct (reg_valid    with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid    with "Hreg Hms")   as %Lms.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Lmenv0.
    iDestruct (reg_valid_dq with "Hreg Hhtif") as %Lhtif.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa0.
    iDestruct (reg_valid_dq with "Hreg Hpma")  as %Lpma0.
    assert (Lmisa : register_lookup misa σa.(sregs) = MISA_C)
      by (rewrite Lmisa0; exact Hmisa_val0).
    assert (Lmenv : register_lookup menvcfg σa.(sregs) = MENVCFG_S)
      by (rewrite Lmenv0; exact Hmenvval0).
    assert (LSXL : _get_Mstatus_SXL (register_lookup mstatus σa.(sregs)) = 'b"10")
      by (rewrite Lms; exact HSXL).
    assert (Lpma : pma_allows_all (register_lookup pma_regions σa.(sregs)))
      by (rewrite Lpma0; exact Hpma_all).
    (* the fetch, through the capability's translation slot (both arms) *)
    iPoseProof (sr_ktier_wit_KT0 strans_regime) as "#Hwtier".
    unshelve iMod (s_regime_fetch strans_regime σa pc (F_Base w) _ _
            Lpc Lpriv Lmisa Lmenv Lhtif LSXL Lpma
            with "Hwtier [$Hreg $Hmem] Htr Hbytes")
      as (σf) "(%Hfetcheq & %Hmdevf & %Hpresf & Hsi & Htr)"; [solve_ndisj |].
    iDestruct ("Hdec" $! σf with "Hsi") as %Hdec0.
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid    with "Hreg Hpriv") as %Hpriv_f.
    iDestruct (reg_valid_dq with "Hreg Help")  as %Help_f.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Hmisa_f.
    iDestruct (reg_valid    with "Hreg Hmenv") as %Hmenv_f.
    specialize (Hdec0 ltac:(rewrite Hpriv_f; reflexivity)
                      ltac:(rewrite Hmisa_f; exact HmisaC)
                      ltac:(rewrite Hmisa_f; exact HmisaA)
                      ltac:(rewrite Hmisa_f; exact Hmisa_val0)
                      ltac:(unfold cfg_ok; right; split;
                            [ exact Hpriv_f | rewrite Hmenv_f; exact Hmenvval0 ])).
    cbn [fetch_is_rvc] in Hdec0.
    assert (Lpc_f : register_lookup PC σf.(sregs) = pc)
      by (rewrite (Hpresf PC ltac:(vm_compute; reflexivity)); exact Lpc).
    assert (Hlpad : eq_vec (register_lookup elp σf.(sregs))
                           (landing_pad_bits_backwards LP_EXPECTED) = false)
      by (rewrite Help_f; exact Help_np).
    (* the execute: at Supervisor, wfi enters the WAIT state *)
    assert (Hpriv_x : register_lookup cur_privilege
                        (set_reg σf nextPC (add_vec_int pc 4)).(sregs) = Supervisor).
    { rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpriv_f | reflexivity ]. }
    pose proof (exec_hart_active_progress_base_gen Supervisor σa σf
                  (set_reg σf nextPC (add_vec_int pc 4)) w (WFI tt) pc
                  (Enter_Wait WAIT_WFI)
                  Lpriv Hdisp Hfetcheq Hdec0 Hlpad Hnlpad Lpc_f
                  (exec_execute_WFI_S _ Hpriv_x) I) as Hha.
    (* the two cells the step writes: nextPC := pc+4, then hart parks *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iMod (reg_update _ hart_state _ (HART_WAITING (WAIT_WFI, zero_extend' 32 w))
            with "Hreg Hhs") as "[Hreg Hhs]".
    iModIntro.
    iExists (set_reg (set_reg σf nextPC (add_vec_int pc 4)) hart_state
               (HART_WAITING (WAIT_WFI, zero_extend' 32 w))).
    iSplitR.
    { iPureIntro.
      exact (exec_riscv_step_wfi_enter σ (set_reg σf nextPC (add_vec_int pc 4))
               (zero_extend' 32 w) mib Hsi Lhs0 Hha). }
    iNext. iModIntro.
    rewrite /mstate_interp. rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem".
    iSplitL "Hmst Hmi". { iExists mst, mib. iFrame. }
    (* ---- and now the WAIT phase, with everything the client is owed
       riding through as [R] ---- *)
    iApply (wp_wfi_wait pc (zero_extend' 32 w)
              (sconf ∗ sie_cap kt m n b p ∗ gpr_file (tp_pin m) ∗ intr_count 0 false)%I
              with "Hminv Hhs Hpcr Hnpc
                    [Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv Hstk Htr Harm Hfile Hcnt]
                    [Hcont]").
    { iSplitL "Hpriv Hms Hhalf Hspp Hmie Hmdl Hmenv".
      { iFrame "Hhw Hminv Hpriv".
        iSplitL "Hms Hhalf Hspp".
        { iExists ms. iFrame "Hms Hhalf Hspp". iPureIntro. exact Hmsf. }
        iSplitL "Hmie Hmdl".
        { iExists mdv0. iFrame "Hmie Hmdl". iPureIntro. exact Hmm. }
        iExists menvcfg0. iFrame "Hmenv". iPureIntro.
        repeat split; assumption. }
      iSplitL "Hstk Htr Harm". { iFrame "Hstk Htr Harm Hwit". }
      iFrame "Hfile Hcnt". }
    iIntros "Hhs' Hpc' (Hsc & Hcap & Hfile & Hcnt)".
    iApply ("Hcont" with "[Hhs' Hsc Hcap Hfile] Hcnt Hpc'").
    iApply (sie_cap_gpr_join with "Hhs' Hsc Hcap Hfile").
  Qed.

End WpSmodeWfi.
