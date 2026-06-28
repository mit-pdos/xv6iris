From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpFetch WpDecode WpEntry WpGpr WpRvc WpAuipc WpGprCsrw WpAdd WpGprAddi WpLoad WpGprLoad WpGprStore WpSmode WpSmode2 WpKernelvec WpPageWalk WpStoreS WpStoreWalk WpStoreS2.
From Kernel Require Import KernelInstrs.
Local Open Scope Z_scope.
Import Defs.

(* WpKvStore.v — WP for kernelvec's first c.sdsp whose store-address translation
   is a page WALK that fills the TLB (discharging the Htr hypothesis of
   wp_pagewalk_csdsp).  The post-execute state carries the tlb fill, so the
   forward engine and step folding get one extra irrelevant_register_set layer
   (tlb) relative to the state-preserving ForwardCsdsp. *)

Section KVS.
  Context `{!riscvGS Σ}.

(* forward engine: like WpStoreS2.ForwardCsdsp but the store EXECUTE fills the
   TLB (s_pc -> set_reg s_pc tlb tlbf), so sXsg's sregs differ from s_pc's. *)
Section ForwardCsdspWalk.
  Context (s : mstate) (pc : mword 64) (b : bool) (w16 : mword 16)
          (cinstr base : instruction) (pa : mword 64) (vrs2 : bv 64)
          (tlbf : vec (option TLB_Entry) (2 ^ 6)).
  Let sAl := set_reg s (R_bool minstret_increment) b.
  Let s_pc := set_reg sAl nextPC (add_vec_int pc 2).
  Let s_pc_f := set_reg s_pc tlb tlbf.
  Let sXsg := MState s_pc_f.(sregs) (write_bytes s_pc_f.(mem) pa 8 vrs2).
  Hypothesis Hfetch_at : exec (fetch tt) sAl = Some (F_RVC w16, sAl).
  Hypothesis Hsi_s : exec (should_inc_minstret Supervisor) s = Some (b, s).
  Hypothesis Hcdec : forall s0,
    eq_vec (_get_Misa_C (register_lookup misa s0.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed w16) s0 = Some (cinstr, s0).
  Hypothesis Hcexec1 : exec (execute cinstr) s_pc = Some (ExecuteAs base, s_pc).
  Hypothesis Hcexec2 : exec (execute base) s_pc = Some (RETIRE_SUCCESS, sXsg).

  Definition sTsg_w : mstate := set_reg sXsg PC (register_lookup nextPC sXsg.(sregs)).
  Definition sFsg_w : mstate :=
    if b then set_reg sTsg_w minstret (add_vec_int (register_lookup minstret sTsg_w.(sregs)) 1)
         else sTsg_w.

  Lemma forward_exec_csdsp_super_walk :
    register_lookup PC s.(sregs) = pc ->
    register_lookup cur_privilege s.(sregs) = Supervisor ->
    exec (dispatchInterrupt Supervisor) sAl = Some (None, sAl) ->
    register_lookup hart_state s.(sregs) = HART_ACTIVE tt ->
    eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
    eq_vec (register_lookup elp s.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false ->
    eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec riscv_step s = Some (tt, sFsg_w).
  Proof using All.
    intros Lpc Lpriv Hdisp Lhs LS Lelp Lmisa.
    assert (LpcA : register_lookup PC sAl.(sregs) = pc).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpc | vm_compute; reflexivity ]. }
    assert (LprivA : register_lookup cur_privilege sAl.(sregs) = Supervisor).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lpriv | vm_compute; reflexivity ]. }
    assert (LhsA : register_lookup hart_state sAl.(sregs) = HART_ACTIVE tt).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lhs | vm_compute; reflexivity ]. }
    assert (LelpA : eq_vec (register_lookup elp sAl.(sregs)) (landing_pad_bits_backwards LP_EXPECTED) = false).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lelp | vm_compute; reflexivity ]. }
    assert (LmisaA : eq_vec (_get_Misa_C (register_lookup misa sAl.(sregs))) ('b"1") = true).
    { unfold sAl, set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ exact Lmisa | vm_compute; reflexivity ]. }
    assert (HdecA : exec (ext_decode_compressed w16) sAl = Some (cinstr, sAl))
      by (apply Hcdec; exact LmisaA).
    assert (Hzca : exec (currentlyEnabled Ext_Zca) sAl = Some (true, sAl))
      by (apply exec_currentlyEnabled_Zca; exact LmisaA).
    assert (Hha : exec (run_hart_active 0) sAl
              = Some (Step_Execute (RETIRE_SUCCESS, zero_extend' 32 w16), sXsg)).
    { exact (exec_hart_active_progress_RVC_gen Supervisor sAl sXsg w16 cinstr base pc RETIRE_SUCCESS
               LprivA Hdisp Hfetch_at HdecA LelpA LpcA Hzca Hcexec1 Hcexec2). }
    apply (exec_riscv_step_gen_gen Supervisor s sXsg (zero_extend' 32 w16) b).
    - exact Lpriv.
    - exact Hsi_s.
    - exact LhsA.
    - exact Hha.
    - unfold sXsg, s_pc_f, s_pc, sAl; cbn [sregs].
      do 3 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lhs.
    - unfold sXsg, s_pc_f, s_pc, sAl; cbn [sregs].
      do 2 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]).
      rewrite register_lookup_set. reflexivity.
    - reflexivity.
  Qed.

  Variable mst0 : mword 64.
  Definition base_upd_sg_super_w : mstate := set_reg sXsg PC (add_vec_int pc 2).
  Definition sFcsg_super_w : mstate :=
    if b then set_reg base_upd_sg_super_w minstret (add_vec_int mst0 1) else base_upd_sg_super_w.

  Lemma sFs_eq_super_walk : register_lookup minstret s.(sregs) = mst0 -> sFsg_w = sFcsg_super_w.
  Proof using All.
    intro Lmst_s.
    assert (Enpc : register_lookup nextPC sXsg.(sregs) = add_vec_int pc 2).
    { unfold sXsg; cbn [sregs]. unfold s_pc_f, s_pc, sAl.
      rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      rewrite register_lookup_set. reflexivity. }
    unfold sFsg_w, sTsg_w, sFcsg_super_w, base_upd_sg_super_w. rewrite Enpc. destruct b; [|reflexivity].
    assert (Emst : register_lookup minstret (set_reg sXsg PC (add_vec_int pc 2)).(sregs) = mst0).
    { unfold set_reg; cbn [sregs]. rewrite irrelevant_register_set; [ | vm_compute; reflexivity ].
      unfold sXsg; cbn [sregs]. unfold s_pc_f, s_pc, sAl, set_reg; cbn [sregs].
      do 3 (rewrite irrelevant_register_set; [ | vm_compute; reflexivity ]). exact Lmst_s. }
    rewrite Emst. reflexivity.
  Qed.
End ForwardCsdspWalk.

End KVS.
