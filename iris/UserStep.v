(* UserStep.v -- step-engine bricks for arbitrary user-mode execution
   (UserExec.v).  First brick: the INTERRUPT DISPATCH decision at User.

   At User privilege the effective mIE and sIE are both unconditionally
   true (priv < M and priv < S): interrupts are architecturally UNMASKABLE,
   and the device loop may raise the sig_seip wire concurrently at any
   time.  So every user-phase step begins with a genuine case split on the
   dispatch decision [u_dispatch] over the CURRENT wire/CSR values:
     - Some (i, Supervisor): a pending delegated interrupt -- the step
       takes the interrupt trap to stvec (the interrupt arm of the step
       obligation, landing in [user_trap_frame]);
     - None: the step proceeds to fetch/execute.
   The M-destined set is empty by [uc_mm] (mie & ~mideleg = 0, a boot
   constant), so a dispatched interrupt always goes to Supervisor.

   [exec_getPendingSet_U_reduce] / [exec_dispatchInterrupt_U_reduce] reduce
   the model's dispatcher to [u_dispatch], parameterized by the current
   register values; the Iris form [dispatch_U_from_regs] takes the cells at
   arbitrary dfracs, so it works both with today's pinned cells and with
   values borrowed from the future invariant shared with the device WP
   (neither the user- nor the kernel-side proofs are plumbed for that
   sharing yet).  Mirrors WpIntrCore's Supervisor reductions
   ([exec_getPendingSet_S_reduce] / [dispatch_S_from_regs]); the User
   variants are simpler because neither mstatus.MIE nor mstatus.SIE is
   consulted below the current privilege.                                 *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras.
Require Import MinstretInv.
Require Import SmodeCore WpIntrCore.
Require Import UserPt UserExec.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The dispatch decision at User: purely the S-destined pending set     *)
(* [s_pending] (no mstatus gate -- both effective enables are true).       *)
(* ===================================================================== *)

Definition u_dispatch (mip_v : mword 64) (meip seip : mword 1)
    (mie_v mdv : mword 64) : option (InterruptType * Privilege) :=
  if neq_vec (s_pending mip_v meip seip mie_v mdv) (zeros' 64)
  then match findPendingInterrupt (s_pending mip_v meip seip mie_v mdv) with
       | Some i => Some (i, Supervisor)
       | None => None
       end
  else None.

Lemma exec_getPendingSet_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (getPendingSet User) s
    = Some ((if neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)
             then Some (s_pending mip_v meip seip mie_v mdv_v, Supervisor)
             else None), s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  assert (Hguard : exec (or_boolM (currentlyEnabled Ext_S)
                     (bind (read_reg mideleg)
                        (fun w1 : mword 64 => returnM (eq_vec w1 (zeros' 64))))) s
                   = Some (true, s)).
  { rewrite (exec_or_boolM_Some _ _ _ _ _ HES). reflexivity. }
  assert (Hae : exec (Defs.assert_exp' true "sys/sys_control.sail:107.58-107.59") s
                = Some (eq_refl, s)).
  { unfold assert_exp'. cbn match. apply exec_returnm. }
  (* effective mIE at User: priv < Machine, so unconditionally true *)
  assert (HmIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Machine))
               (bind (read_reg mstatus)
                  (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1")))))
            (returnM (orb (generic_eq User Supervisor) (generic_eq User User)))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Machine))
                     (bind (read_reg mstatus)
                        (fun w7 : mword 64 => returnM (eq_vec (_get_Mstatus_MIE w7) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Machine) s)).
      change (generic_eq User Machine) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (orb (generic_eq User Supervisor) (generic_eq User User)) with true.
    apply exec_returnm. }
  (* effective sIE at User: priv < Supervisor, so unconditionally true *)
  assert (HsIEt : exec (or_boolM
            (and_boolM (returnM (generic_eq User Supervisor))
               (bind (read_reg mstatus)
                  (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1")))))
            (returnM (generic_eq User User))) s
                = Some (true, s)).
  { assert (Hand : exec (and_boolM (returnM (generic_eq User Supervisor))
                     (bind (read_reg mstatus)
                        (fun w : mword 64 => returnM (eq_vec (_get_Mstatus_SIE w) ('b"1"))))) s
                   = Some (false, s)).
    { rewrite (exec_and_boolM_Some _ _ _ _ _ (exec_returnM (generic_eq User Supervisor) s)).
      change (generic_eq User Supervisor) with false. reflexivity. }
    rewrite (exec_or_boolM_Some _ _ _ _ _ Hand).
    change (generic_eq User User) with true.
    apply exec_returnm. }
  unfold getPendingSet.
  rewrite (exec_bind_Some _ _ _ _ _ Hguard).
  rewrite (exec_bind_Some _ _ _ _ _ Hae).
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_read_mip_reduce s mip_v meip seip HES Hmip Hmeip Hseip)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mie s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg mideleg s)).
  rewrite (exec_bind_Some _ _ _ _ _ HmIEt).
  rewrite (exec_bind_Some _ _ _ _ _ HsIEt).
  rewrite Hmie Hmdl Hmm.
  rewrite and_vec_zeros64_r.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq.
  rewrite andb_false_r andb_true_l.
  unfold s_pending, s_mip_bits.
  apply exec_returnm.
Qed.

Lemma exec_dispatchInterrupt_U_reduce (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt User) s
    = Some (u_dispatch mip_v meip seip mie_v mdv_v, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm.
  unfold dispatchInterrupt.
  rewrite (exec_bind_Some _ _ _ _ _
            (exec_getPendingSet_U_reduce s mip_v mie_v mdv_v meip seip
               HES Hmip Hmeip Hseip Hmie Hmdl Hmm)).
  unfold u_dispatch.
  destruct (neq_vec (s_pending mip_v meip seip mie_v mdv_v) (zeros' 64)).
  - cbn match. destruct (findPendingInterrupt (s_pending mip_v meip seip mie_v mdv_v));
      apply exec_returnm.
  - cbn match. apply exec_returnm.
Qed.

(* the no-pending corollary: with the S-destined set empty AT THIS STEP,
   the dispatcher is a no-op and the step proceeds to fetch/execute *)
Lemma exec_dispatchInterrupt_U_none (s : mstate)
    (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1) :
  exec (currentlyEnabled Ext_S) s = Some (true, s) ->
  register_lookup mip s.(sregs) = mip_v ->
  register_lookup sig_meip s.(sregs) = meip ->
  register_lookup sig_seip s.(sregs) = seip ->
  register_lookup mie s.(sregs) = mie_v ->
  register_lookup mideleg s.(sregs) = mdv_v ->
  and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
  and_vec (s_mip_bits mip_v meip seip) (and_vec mie_v mdv_v) = zeros' 64 ->
  exec (dispatchInterrupt User) s = Some (None, s).
Proof.
  intros HES Hmip Hmeip Hseip Hmie Hmdl Hmm Hs0.
  rewrite (exec_dispatchInterrupt_U_reduce s mip_v mie_v mdv_v meip seip
             HES Hmip Hmeip Hseip Hmie Hmdl Hmm).
  unfold u_dispatch, s_pending. rewrite Hs0.
  assert (Hnq : neq_vec (zeros' 64 : mword 64) (zeros' 64) = false)
    by (vm_compute; reflexivity).
  rewrite Hnq. reflexivity.
Qed.

(* ===================================================================== *)
(* §1b The WAITING-hart step (a user WRS.STO/NTO suspended the core).      *)
(* [run_hart_waiting] at exit_wait = false (riscv_step's fixed argument)   *)
(* either WAKES -- an interrupt bit is pending in the raw mip & mie        *)
(* ([shouldWakeForInterrupt]), or the reservation is invalid -- and        *)
(* retires (hart_state := ACTIVE, PC ticks, minstret bumps), or STAYS      *)
(* waiting (the ONLY state change is the wrapper's minstret_increment      *)
(* write; no PC tick).  [valid_reservation] is an OPAQUE platform axiom,   *)
(* so the step proof case-splits on it -- BOTH branches step.              *)
(* ===================================================================== *)

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

(* wake because an interrupt bit is pending (any wait reason) *)
Lemma exec_run_hart_waiting_wake (wr : WaitReason) (ib : mword 32) (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = true ->
  exec (run_hart_waiting 0 wr ib false) s
    = Some (Step_Execute (Retire_Success tt, ib),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hw.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  change (get_config_print_instr tt) with false. cbn match.
  (* the print-skip [returnM tt] and the hart_state write both compute away
     inside the peeled prefix (exec evaluates the RegWrite outcome) *)
  erewrite exec_bind0_Some. 2: apply exec_returnm.
  apply exec_returnm.
Qed.

(* wake because the reservation is invalid (WRS waits only) *)
Lemma exec_run_hart_waiting_wake_resv (wr : WaitReason) (ib : mword 32) (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = false ->
  valid_reservation tt = false ->
  wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO ->
  exec (run_hart_waiting 0 wr ib false) s
    = Some (Step_Execute (Retire_Success tt, ib),
            set_reg s hart_state (HART_ACTIVE tt)).
Proof.
  intros Hw Hvr Hwr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  rewrite Hvr.
  destruct Hwr as [-> | ->]; cbn match;
    (change (get_config_print_instr tt) with false; cbn match;
     erewrite exec_bind0_Some; [| apply exec_returnm];
     apply exec_returnm).
Qed.

(* stay waiting: no interrupt pending and the reservation is (still) valid *)
Lemma exec_run_hart_waiting_stay (wr : WaitReason) (ib : mword 32) (s : mstate) :
  neq_vec (and_vec (register_lookup mip s.(sregs))
                   (register_lookup mie s.(sregs))) (zeros' 64) = false ->
  valid_reservation tt = true ->
  exec (run_hart_waiting 0 wr ib false) s = Some (Step_Waiting wr, s).
Proof.
  intros Hw Hvr.
  unfold run_hart_waiting.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_shouldWakeForInterrupt s)). cbn beta.
  rewrite Hw. cbn match.
  rewrite Hvr.
  destruct wr; cbn match;
    (change (get_config_print_instr tt) with false; cbn match;
     erewrite exec_bind0_Some; [| apply exec_returnm];
     apply exec_returnm).
Qed.

(* --------------------------------------------------------------------- *)
(* The try_step wrappers.  STAY: the whole step is the wrapper's           *)
(* minstret_increment write (the epilogue sees a WAITING hart and skips    *)
(* the PC tick and the bump).  WAKE: the Retire_Success tail is exactly    *)
(* the retiring-instruction epilogue (tick + conditional bump).            *)
(* --------------------------------------------------------------------- *)

Section StepWaitStay.
  Context (s : mstate) (wr : WaitReason) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Hypothesis Hhart : register_lookup hart_state s_a.(sregs) = HART_WAITING (wr, ib).
  Hypothesis Hrhw :
    exec (run_hart_waiting 0 wr ib false) s_a = Some (Step_Waiting wr, s_a).

  Lemma exec_riscv_step_wait_stay : exec (riscv_step false) s = Some (tt, s_a).
  Proof using All.
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (true, s_a))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hrhw). cbn beta.
    cbn match.
    (* Step_Waiting arm: read hart_state >>= assert hart_is_waiting *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart. unfold Defs.assert_exp. cbn [hart_is_waiting].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart. cbn beta iota.
    apply exec_returnm.
  Qed.
End StepWaitStay.

Section StepWaitWake.
  Context (s : mstate) (wr : WaitReason) (ib : mword 32) (b : bool).
  Hypothesis Hsi :
    exec (should_inc_minstret (register_lookup cur_privilege s.(sregs))) s
      = Some (b, s).
  Let s_a : mstate := set_reg s (R_bool minstret_increment) b.
  Let s_w : mstate := set_reg s_a hart_state (HART_ACTIVE tt).
  Hypothesis Hhart : register_lookup hart_state s_a.(sregs) = HART_WAITING (wr, ib).
  (* stated via the FOLDED [s_w] so every derived term downstream stays
     folded and the epilogue rewrites match syntactically *)
  Hypothesis Hrhw :
    exec (run_hart_waiting 0 wr ib false) s_a
      = Some (Step_Execute (Retire_Success tt, ib), s_w).

  Let s_tick : mstate := set_reg s_w PC (register_lookup nextPC s_w.(sregs)).
  Let s_final : mstate :=
    if b then set_reg s_tick minstret
                      (add_vec_int (register_lookup minstret s_tick.(sregs)) 1)
         else s_tick.

  Lemma exec_riscv_step_wait_wake : exec (riscv_step false) s = Some (tt, s_final).
  Proof using All.
    assert (Hhart_w : register_lookup hart_state s_w.(sregs) = HART_ACTIVE tt).
    { unfold s_w, set_reg; cbn [sregs]. apply register_lookup_set. }
    unfold riscv_step.
    rewrite (exec_bind_Some _ _ _ _ _
              (_ : exec (try_step 0 false) s = Some (false, s_final))).
    { reflexivity. }
    unfold try_step.
    cbn [ext_pre_step_hook].
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). cbn beta.
    rewrite (exec_bind_Some _ _ _ _ _ Hsi). cbn beta.
    rewrite (exec_bind0_Some _ _ _ _ _ (exec_write_reg (R_bool minstret_increment) b s)).
    rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg hart_state s_a)). cbn beta.
    rewrite Hhart. cbn beta iota.
    rewrite (exec_bind_Some _ _ _ _ _ Hrhw). cbn beta.
    cbn match.
    (* Retire_Success arm: read hart_state >>= assert hart_is_active *)
    erewrite exec_bind_Some.
    2:{ erewrite exec_bind0_Some.
        2:{ erewrite exec_bind_Some.
            2:{ apply exec_read_reg. }
            rewrite Hhart_w. unfold Defs.assert_exp. cbn [hart_is_active].
            reflexivity. }
        apply exec_read_reg. }
    rewrite Hhart_w. cbn beta iota.
    erewrite exec_bind0_Some.
    2:{ apply exec_tick_pc. }
    erewrite exec_bind_Some.
    2:{ unfold Defs.and_boolM.
        erewrite exec_bind_Some.
        2:{ reflexivity. }
        cbn beta iota. apply (exec_read_reg minstret_increment). }
    change (get_config_rvfi tt) with false.
    replace (register_lookup minstret_increment
               (set_reg s_w PC (register_lookup nextPC s_w.(sregs))).(sregs))
      with b.
    2:{ unfold s_w, s_a, set_reg; cbn [sregs].
        repeat (first [ rewrite register_lookup_set
                      | rewrite irrelevant_register_set; [ | vm_compute; reflexivity ] ]).
        reflexivity. }
    unfold s_final, s_tick.
    destruct b.
    - erewrite exec_bind0_Some.
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
End StepWaitWake.

(* ===================================================================== *)
(* §2 The frame-level form: the dispatch decision from BORROWED cells.     *)
(* All cells are dfrac-generic, so the wire cells (sig_meip / sig_seip)    *)
(* can come from the future invariant shared with the device WP -- the     *)
(* engine opens it, applies this with the current wire values, and closes  *)
(* it before the step commits.                                             *)
(* ===================================================================== *)
Section UserStepIris.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma dispatch_U_from_regs (σ : mstate)
      (mip_v mie_v mdv_v : mword 64) (meip seip : mword 1)
      {dqp dqe1 dqe2 dqi dqd : dfrac} :
    and_vec mie_v (not_vec mdv_v) = zeros' 64 ->
    hw_config -∗
    mstate_interp σ -∗
    mip ↦ᵣ{ dqp } mip_v -∗
    sig_meip ↦ᵣ{ dqe1 } meip -∗
    sig_seip ↦ᵣ{ dqe2 } seip -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    mideleg ↦ᵣ{ dqd } mdv_v -∗
    ⌜exec (dispatchInterrupt User) σ
       = Some (u_dispatch mip_v meip seip mie_v mdv_v, σ)⌝.
  Proof.
    iIntros (Hmm) "Hhw [Hreg [Hmem Hdev]] Hmip Hmeip Hseip Hmie Hmdl".
    iDestruct "Hhw" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & _ & _ & _ & _ & %HmisaS & _)".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    iDestruct (reg_valid_dq with "Hreg Hmip")  as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmeip") as %Lmeip.
    iDestruct (reg_valid_dq with "Hreg Hseip") as %Lseip.
    iDestruct (reg_valid_dq with "Hreg Hmie")  as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmdl")  as %Lmdl.
    iPureIntro.
    apply exec_dispatchInterrupt_U_reduce; try assumption.
    rewrite exec_currentlyEnabled_S. rewrite Lmisa. rewrite HmisaS. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The WAITING-hart step arm: one machine step from a WRS-suspended      *)
  (* hart either STAYS waiting (nothing observable changes) or WAKES and   *)
  (* retires (hart_state := ACTIVE, PC ticks to nextPC).  The proof        *)
  (* case-splits on the wake condition (raw mip & mie over the given cell  *)
  (* values) and, when that is clear, on the OPAQUE [valid_reservation]    *)
  (* axiom -- both branches step, so the arm is total.  The continuation   *)
  (* is an ADDITIVE conjunction: stay / wake.                              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_user_step_waiting Φ (wr : WaitReason) (ib : mword 32)
      (mip_v mie_v : mword 64) (va va' : mword 64) {dqp dqi : dfrac} :
    wr = WAIT_WRS_STO \/ wr = WAIT_WRS_NTO ->
    minstret_inv -∗
    hart_state ↦ᵣ HART_WAITING (wr, ib) -∗
    PC ↦ᵣ va -∗
    nextPC ↦ᵣ va' -∗
    mip ↦ᵣ{ dqp } mip_v -∗
    mie ↦ᵣ{ dqi } mie_v -∗
    ▷ ((hart_state ↦ᵣ HART_WAITING (wr, ib) -∗ PC ↦ᵣ va -∗ nextPC ↦ᵣ va' -∗
        mip ↦ᵣ{ dqp } mip_v -∗ mie ↦ᵣ{ dqi } mie_v -∗
        WP (Loop : expr riscv_lang) {{ Φ }})
     ∧ (hart_state ↦ᵣ HART_ACTIVE tt -∗ PC ↦ᵣ va' -∗ nextPC ↦ᵣ va' -∗
        mip ↦ᵣ{ dqp } mip_v -∗ mie ↦ᵣ{ dqi } mie_v -∗
        WP (Loop : expr riscv_lang) {{ Φ }})) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros (Hwr) "#Hinv Hhs Hpc Hnpc Hmip Hmie Hcont".
    iApply (wp_exec_step_minstret (⊤ ∖ ↑minstretN) Φ with "Hinv").
    iIntros (σ) "[Hreg Hmd] Hbody".
    iDestruct "Hbody" as (mst mi_old) "[Hmst Hmi]".
    iDestruct (reg_valid_dq with "Hreg Hhs") as %Lhs.
    iDestruct (reg_valid_dq with "Hreg Hnpc") as %Lnpc.
    iDestruct (reg_valid_dq with "Hreg Hmip") as %Lmip.
    iDestruct (reg_valid_dq with "Hreg Hmie") as %Lmie.
    iDestruct (reg_valid_dq with "Hreg Hmst") as %Lmst.
    destruct (exec_should_inc_minstret_Some
                (register_lookup cur_privilege σ.(sregs)) σ) as [b Hsi].
    iMod (reg_update _ (R_bool minstret_increment) _ b with "Hreg Hmi") as "[Hreg Hmi]".
    set (s_a := set_reg σ (R_bool minstret_increment) b).
    assert (Lhs_a : register_lookup hart_state s_a.(sregs) = HART_WAITING (wr, ib)).
    { unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lhs | reflexivity]. }
    assert (Lmip_a : register_lookup mip s_a.(sregs) = mip_v).
    { unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmip | reflexivity]. }
    assert (Lmie_a : register_lookup mie s_a.(sregs) = mie_v).
    { unfold s_a, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [exact Lmie | reflexivity]. }
    destruct (neq_vec (and_vec mip_v mie_v) (zeros' 64)) eqn:Hwake;
      [ | destruct (valid_reservation tt) eqn:Hvr ].
    - (* WAKE: an interrupt bit is pending in raw mip & mie *)
      assert (Hrhw : exec (run_hart_waiting 0 wr ib false) s_a
                     = Some (Step_Execute (Retire_Success tt, ib),
                             set_reg s_a hart_state (HART_ACTIVE tt))).
      { apply exec_run_hart_waiting_wake. rewrite Lmip_a Lmie_a. exact Hwake. }
      pose proof (exec_riscv_step_wait_wake σ wr ib b Hsi Lhs_a Hrhw) as Hstep.
      set (T0 := set_reg s_a hart_state (HART_ACTIVE tt)) in Hstep.
      assert (Hnpc0 : register_lookup nextPC T0.(sregs) = va').
      { unfold T0, s_a, set_reg; cbn [sregs].
        repeat (rewrite irrelevant_register_set; [ | reflexivity ]).
        exact Lnpc. }
      rewrite Hnpc0 in Hstep.
      set (T1 := set_reg T0 PC va') in Hstep.
      assert (Hmst1 : register_lookup minstret T1.(sregs) = mst).
      { unfold T1, T0, s_a, set_reg; cbn [sregs].
        repeat (rewrite irrelevant_register_set; [ | reflexivity ]).
        exact Lmst. }
      rewrite Hmst1 in Hstep.
      destruct b.
      + iModIntro. iExists (set_reg T1 minstret (add_vec_int mst 1)).
        iSplitR. { iPureIntro. exact Hstep. }
        iNext.
        iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
        iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
        iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro.
        unfold T1, T0, s_a, set_reg; cbn [sregs mem mdev].
        iFrame "Hreg Hmd".
        iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
        iDestruct "Hcont" as "[_ Hwake']".
        iApply ("Hwake'" with "Hhs Hpc Hnpc Hmip Hmie").
      + iModIntro. iExists T1.
        iSplitR. { iPureIntro. exact Hstep. }
        iNext.
        iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
        iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
        iModIntro.
        unfold T1, T0, s_a, set_reg; cbn [sregs mem mdev].
        iFrame "Hreg Hmd".
        iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
        iDestruct "Hcont" as "[_ Hwake']".
        iApply ("Hwake'" with "Hhs Hpc Hnpc Hmip Hmie").
    - (* STAY: no interrupt pending, reservation (still) valid *)
      assert (Hrhw : exec (run_hart_waiting 0 wr ib false) s_a
                     = Some (Step_Waiting wr, s_a)).
      { apply exec_run_hart_waiting_stay; [ | exact Hvr ].
        rewrite Lmip_a Lmie_a. exact Hwake. }
      pose proof (exec_riscv_step_wait_stay σ wr ib b Hsi Lhs_a Hrhw) as Hstep.
      iModIntro. iExists s_a.
      iSplitR. { iPureIntro. exact Hstep. }
      iNext. iModIntro.
      unfold s_a, set_reg; cbn [sregs mem mdev].
      iFrame "Hreg Hmd".
      iSplitL "Hmst Hmi". { iExists mst, b. iFrame. }
      iDestruct "Hcont" as "[Hstay _]".
      iApply ("Hstay" with "Hhs Hpc Hnpc Hmip Hmie").
    - (* WAKE: the reservation is invalid *)
      assert (Hrhw : exec (run_hart_waiting 0 wr ib false) s_a
                     = Some (Step_Execute (Retire_Success tt, ib),
                             set_reg s_a hart_state (HART_ACTIVE tt))).
      { apply exec_run_hart_waiting_wake_resv; [ | exact Hvr | exact Hwr ].
        rewrite Lmip_a Lmie_a. exact Hwake. }
      pose proof (exec_riscv_step_wait_wake σ wr ib b Hsi Lhs_a Hrhw) as Hstep.
      set (T0 := set_reg s_a hart_state (HART_ACTIVE tt)) in Hstep.
      assert (Hnpc0 : register_lookup nextPC T0.(sregs) = va').
      { unfold T0, s_a, set_reg; cbn [sregs].
        repeat (rewrite irrelevant_register_set; [ | reflexivity ]).
        exact Lnpc. }
      rewrite Hnpc0 in Hstep.
      set (T1 := set_reg T0 PC va') in Hstep.
      assert (Hmst1 : register_lookup minstret T1.(sregs) = mst).
      { unfold T1, T0, s_a, set_reg; cbn [sregs].
        repeat (rewrite irrelevant_register_set; [ | reflexivity ]).
        exact Lmst. }
      rewrite Hmst1 in Hstep.
      destruct b.
      + iModIntro. iExists (set_reg T1 minstret (add_vec_int mst 1)).
        iSplitR. { iPureIntro. exact Hstep. }
        iNext.
        iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
        iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
        iMod (reg_update _ minstret _ (add_vec_int mst 1) with "Hreg Hmst") as "[Hreg Hmst]".
        iModIntro.
        unfold T1, T0, s_a, set_reg; cbn [sregs mem mdev].
        iFrame "Hreg Hmd".
        iSplitL "Hmst Hmi". { iExists (add_vec_int mst 1), true. iFrame. }
        iDestruct "Hcont" as "[_ Hwake']".
        iApply ("Hwake'" with "Hhs Hpc Hnpc Hmip Hmie").
      + iModIntro. iExists T1.
        iSplitR. { iPureIntro. exact Hstep. }
        iNext.
        iMod (reg_update _ hart_state _ (HART_ACTIVE tt) with "Hreg Hhs") as "[Hreg Hhs]".
        iMod (reg_update _ PC _ va' with "Hreg Hpc") as "[Hreg Hpc]".
        iModIntro.
        unfold T1, T0, s_a, set_reg; cbn [sregs mem mdev].
        iFrame "Hreg Hmd".
        iSplitL "Hmst Hmi". { iExists mst, false. iFrame. }
        iDestruct "Hcont" as "[_ Hwake']".
        iApply ("Hwake'" with "Hhs Hpc Hnpc Hmip Hmie").
  Qed.

End UserStepIris.

(* ===================================================================== *)
(* §3 The step obligation, reduced to its ACTIVE-hart residue: the        *)
(* WAITING case (a user WRS suspended the core) is discharged here via    *)
(* [wp_user_step_waiting] -- both the stay and the wake outcome re-enter  *)
(* [user_inv].                                                            *)
(* ===================================================================== *)
Section UserStepObligation.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.
  Context (C : ucfg) (pt : upt).

  Theorem user_step_obligation_holds (Φ : mval -> iProp Σ) :
    minstret_inv -∗
    user_step_obligation_active C pt Φ -∗
    user_step_obligation C pt Φ.
  Proof.
    iIntros "#Hminstret #Hactive".
    iIntros "!> Hinv Hk".
    iDestruct "Hinv" as (hs ms_v sc_v stval_v sepc_v va va' g)
      "(%Hhs & %Hms & %Hlock & Hregs & Hupt & Hcfg)".
    destruct hs as [u | [wr ib]].
    - (* ACTIVE: hand off to the residue obligation *)
      destruct u.
      rewrite (Hlock tt eq_refl).
      iApply ("Hactive" with "[//] Hregs Hupt Hcfg Hk").
    - (* WAITING: the WRS stay/wake step *)
      simpl in Hhs.
      iDestruct "Hregs" as "(Hhs & Hpriv & Hms & Hsc & Hstval & Hsepc &
                             Hpc & Hnpc & Hgpr)".
      iDestruct "Hcfg" as "(Hstvec & Hmie & Hmdl & Hmedl & Hmip & Hcfgrest)".
      iApply (wp_user_step_waiting Φ wr ib (uc_mip C) (uc_mie C) va va' Hhs
                with "Hminstret Hhs Hpc Hnpc Hmip Hmie [-]").
      iNext. iSplit.
      + (* STAY: re-enter [user_inv] with the same waiting machine *)
        iIntros "Hhs Hpc Hnpc Hmip Hmie".
        iDestruct "Hk" as "[Hk _]".
        iApply "Hk".
        iExists (HART_WAITING (wr, ib)), ms_v, sc_v, stval_v, sepc_v, va, va', g.
        iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt".
        iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
        iPureIntro. split; [exact Hhs | split; [exact Hms | intros u Hu; discriminate Hu]].
      + (* WAKE: re-enter [user_inv] ACTIVE, pc in lock-step at [va'] *)
        iIntros "Hhs Hpc Hnpc Hmip Hmie".
        iDestruct "Hk" as "[Hk _]".
        iApply "Hk".
        iExists (HART_ACTIVE tt), ms_v, sc_v, stval_v, sepc_v, va', va', g.
        iFrame "Hhs Hpriv Hms Hsc Hstval Hsepc Hpc Hnpc Hgpr Hupt".
        iFrame "Hstvec Hmie Hmdl Hmedl Hmip Hcfgrest".
        iPureIntro. split; [exact Hms | intros u _; reflexivity].
  Qed.

  (* the capstone, over the ACTIVE residue only: what remains of the whole
     user-execution theorem is [user_step_obligation_active] *)
  Corollary wp_user_exec_active (Φ : mval -> iProp Σ) :
    minstret_inv -∗
    user_step_obligation_active C pt Φ -∗
    user_inv C pt -∗
    stvec_handler_wp C pt Φ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    iIntros "#Hminstret #Hactive Hinv Htrap".
    iApply (wp_user_exec with "[] Hinv Htrap").
    iApply (user_step_obligation_holds Φ with "Hminstret Hactive").
  Qed.

End UserStepObligation.

(* (The old §4 full-WP RETIRING step engine [wp_user_step_retire] is gone:
   the payload-form [retire_branch] (UserArms.v) supersedes it -- the
   unified step wrapper owns the single step, so the retire arm produces
   the [wp_exec_step_minstret] payload instead of opening its own step.)   *)

(* ===================================================================== *)
(* §5 The decode-bridge agreement: the user frame's pins coincide with     *)
(* the U-mode reference decode state on every register the decoder reads.  *)
(* ===================================================================== *)
Require Import WpDecodeBridge DecodeTotalU.

Lemma agree_u (σ : mstate) :
  register_lookup cur_privilege σ.(sregs) = User ->
  register_lookup menvcfg σ.(sregs) = MENVCFG_S ->
  register_lookup senvcfg σ.(sregs) = (mword_of_int 0 : mword 64) ->
  register_lookup mstateen0 σ.(sregs) = (mword_of_int 0 : mword 64) ->
  register_lookup sstateen0 σ.(sregs) = (mword_of_int 0 : mword 32) ->
  register_lookup misa σ.(sregs) = MISA_C ->
  agree_on D_u σ dstateU.
Proof.
  intros Hpriv Hmenv Hsenv Hms0 Hss0 Hmisa r Hr.
  unfold D_u in Hr.
  repeat (apply orb_prop in Hr; destruct Hr as [Hr | Hr]);
    apply register_beq_true in Hr; subst r;
    [ rewrite Hpriv | rewrite Hmenv | rewrite Hsenv
    | rewrite Hms0 | rewrite Hss0 | rewrite Hmisa ];
    first [ vm_compute; reflexivity
          | apply bv_eq; vm_compute; reflexivity ].
Qed.

(* the U-mode decode image contains no landing-pad instruction (the
   Zicfilp gate is off at dstateU), so the lpad side condition of the
   run_hart_active dispatch discharges for every decodable word *)
Require Import DecodeSetU.

Lemma decodable_u_not_lpad (i : instruction) :
  decodable_u i = true -> is_lpad_instruction i = false.
Proof.
  intro Hd. destruct i; first [ reflexivity | discriminate Hd ].
Qed.

Lemma decodable_c_not_lpad (i : instruction) :
  decodable_c i = true -> is_lpad_instruction i = false.
Proof.
  intro Hd. destruct i; first [ reflexivity | discriminate Hd ].
Qed.

(* ===================================================================== *)
(* §6 The BASE one-redirection progress composer: a 4-byte instruction    *)
(* whose execute returns [ExecuteAs other] (SINVAL_VMA -> SFENCE_VMA).    *)
(* [exec_hart_active_progress_base_gen] (SmodeCore.v) forbids ExecuteAs   *)
(* and [_RVC_gen] redirects only on the compressed path; this is the      *)
(* missing base-path redirect, same shape as both.                        *)
(* ===================================================================== *)
Lemma exec_hart_active_progress_base_redirect_gen
    (priv : Privilege) (s s_f s_x : mstate) (w : mword 32) (instr other : instruction)
    (pc : mword 64) (resf : ExecutionResult) :
  register_lookup cur_privilege s.(sregs) = priv ->
  exec (dispatchInterrupt priv) s = Some (None, s) ->
  exec (fetch tt) s = Some (F_Base w, s_f) ->
  exec (ext_decode w) s_f = Some (instr, s_f) ->
  eq_vec (register_lookup elp s_f.(sregs))
         (landing_pad_bits_backwards LP_EXPECTED) = false ->
  is_lpad_instruction instr = false ->
  register_lookup PC s_f.(sregs) = pc ->
  exec (execute instr) (set_reg s_f nextPC (add_vec_int pc 4))
    = Some (ExecuteAs other, set_reg s_f nextPC (add_vec_int pc 4)) ->
  exec (execute other) (set_reg s_f nextPC (add_vec_int pc 4)) = Some (resf, s_x) ->
  exec (run_hart_active 0) s = Some (Step_Execute (resf, zero_extend' 32 w), s_x).
Proof.
  intros Hpriv Hdisp Hfetch Hdec Hlpad Hnotlpad HpcF Hexec Hexec2.
  unfold run_hart_active.
  rewrite exec_catch_early_return.
  rewrite execR_bind execR_liftR exec_read_reg Hpriv. cbn match.
  rewrite execR_bind execR_liftR Hdisp. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  rewrite execR_liftR Hfetch. cbn match. cbn match.
  unfold ext_fetch_hook. cbn match. cbn beta iota.
  rewrite execR_bind execR_liftR Hdec. cbn match.
  unfold get_config_print_instr. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_returnR. cbn match.
  unfold and_boolM.
  rewrite execR_bind execR_liftR exec_is_landing_pad Hlpad. cbn match. cbn match.
  rewrite execR_returnR. cbn match. cbn match.
  rewrite execR_bind execR_liftR (exec_read_reg PC) HpcF. cbn match.
  rewrite execR_bind. rewrite execR_bind0 execR_liftR (exec_write_reg nextPC). cbn match.
  rewrite execR_liftR Hexec. cbn match. cbn match.
  rewrite execR_bind execR_liftR Hexec2. cbn match.
  rewrite execR_returnR. cbn match. reflexivity.
Qed.
