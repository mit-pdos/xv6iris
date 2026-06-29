From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import MinstretInv.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2 WpKvStore WpGprMret WpGprSret WpKvJal.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvSret.v — wp_kv_sret, the kernelvec `sret` @0x8000542c (4-byte NON-RVC,
   Supervisor superpage).  Fetches F_Base, executes SRET (exec_execute_SRET),
   returning to PC = aligned sepc in privilege `newpriv` (= if SPP then
   Supervisor else User).  Forward engine is the BASE (non-RVC) Supervisor
   step with an ABSTRACT post-execute state sX. *)

Section ForwardSRETsup.
  Context `{!riscvGS Σ}.
  Context (root_ppn : mword 44).
  Context (s : mstate) (pc : mword 64) (b : bool) (w : mword 32) (sX : mstate).
  Hypothesis Hfetch_at :
    exec (fetch tt) (set_reg s (R_bool minstret_increment) b)
      = Some (F_Base w, set_reg s (R_bool minstret_increment) b).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hdec : forall s0, register_lookup cur_privilege (sregs s0) = Supervisor ->
    exec (ext_decode w) s0 = Some (SRET tt, s0).
  Hypothesis Hdisp_s : exec (dispatchInterrupt Supervisor) (set_reg s (R_bool minstret_increment) b) = Some (None, set_reg s (R_bool minstret_increment) b).
  Hypothesis HexecS :
    exec (execute (SRET tt)) (set_reg (set_reg s (R_bool minstret_increment) b) nextPC (add_vec_int pc 4))
      = Some (RETIRE_SUCCESS, sX).
  Hypothesis Hhart_X : register_lookup hart_state sX.(sregs) = HART_ACTIVE tt.
  Hypothesis Hmi_X : register_lookup (R_bool minstret_increment) sX.(sregs) = b.

  Definition sAsr : mstate := set_reg s (R_bool minstret_increment) b.
  Definition s_pcsr : mstate := set_reg sAsr nextPC (add_vec_int pc 4).
  Definition sTsr : mstate := set_reg sX PC (register_lookup nextPC sX.(sregs)).
  Definition sFsr : mstate :=
    if b then set_reg sTsr minstret (add_vec_int (register_lookup minstret sTsr.(sregs)) 1)
         else sTsr.

  Lemma forward_exec_sret_sup :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    exec riscv_step s = Some (tt, sFsr).
  Proof using All.
    intros Lpc Lpriv Lhs Lelp.
    assert (LpcA  : register_lookup PC sAsr.(sregs) = pc).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA: register_lookup cur_privilege sAsr.(sregs) = Supervisor).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA  : register_lookup hart_state sAsr.(sregs) = HART_ACTIVE tt).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAsr.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAsr, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (HfetchA : exec (fetch tt) sAsr = Some (F_Base w, sAsr)) by exact Hfetch_at.
    assert (HdecA : exec (ext_decode w) sAsr = Some (SRET tt, sAsr)) by (apply Hdec; exact LprivA).
    assert (HexecA : exec (execute (SRET tt)) s_pcsr = Some (RETIRE_SUCCESS, sX)) by exact HexecS.
    assert (Hha : exec (run_hart_active 0) sAsr = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w), sX)).
    { exact (exec_hart_active_progress_gen root_ppn Supervisor sAsr sAsr sX sAsr w
               (SRET tt) pc RETIRE_SUCCESS
               LprivA Hdisp_s HfetchA HdecA LelpA ltac:(reflexivity) LpcA HexecA I). }
    apply (exec_riscv_step_gen_gen Supervisor s sX (zero_extend' 32 w) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - exact Hhart_X.
    - exact Hmi_X.
    - reflexivity.
  Qed.
End ForwardSRETsup.
