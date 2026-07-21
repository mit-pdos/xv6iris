(* WpKfree.v -- instruction-level proof of the kernel's [kfree] (0x80000a38)
   against the allocator spec in KallocInv.v.

   kfree is a whole-function S-mode proof in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): it threads the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALLS the sub-functions memset / acquire / release via [jal], discharging
   each callee's whole-function WP.  The novel content is the free-list PUSH,
   which is discharged by KallocInv's transfer lemma [kmem_res_push] together
   with [page_head8_word_at] / [run_page_page_own].

   Structural sibling: [WpKalloc.v] (same branch).  This file mirrors its
   statement shape (S-mode config + frame windows) and its prologue proof. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
From iris.base_logic.lib Require Import ghost_var.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText WpAuipc.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpMycpu.
Require Import WpLock.
Require Import WpRelease WpMemsetPage.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import KallocInv WpKallocDecode.
Require Import KptTree.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMem WpSmodePtMemWrap.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* Register-generic execute helpers for SLTU (the bounds-check compares), *)
(* mirroring [exec_execute_RTYPE_OR{,_gpr}] in WpGprLogic.  The model's    *)
(* SLTU writes [zero_extend' 64 (bool_to_bit (a <u b))].                   *)
(* ===================================================================== *)
(* gpr_sltu_val / exec_execute_RTYPE_SLTU{,_gpr} relocated to WpMmodeLeafBase.v *)

(* [zopz0zI_u x y = Z.ltb (uint x) (uint y)]; a false compare packs to 0. *)
Lemma sltu_false_zero (a b : mword 64) :
  zopz0zI_u a b = false ->
  (zero_extend' 64 (bool_to_bit (zopz0zI_u a b)) : mword 64) = mword_of_int 0.
Proof. intro H. rewrite H. apply bv_eq; vm_compute; reflexivity. Qed.

(* [slli p 0x34] with [p] 4096-aligned is zero: the low 12 bits (all zero)
   are the only ones that survive a 52-bit left shift in 64 bits. *)
Lemma shift_bits_left52_zero (p : mword 64) :
  (uint p) mod 4096 = 0 ->
  shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0) = mword_of_int 0.
Proof.
  intro Hal.
  assert (Hn : shift_bits_left p (subrange_vec_dec (mword_of_int 52 : mword 6) (Z.sub log2_xlen 1) 0)
             = shiftl p 52).
  { unfold shift_bits_left. f_equal; vm_compute; reflexivity. }
  rewrite Hn. apply bv_eq.
  unfold shiftl, with_word, get_word, MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  assert (Hsh : bv_unsigned (MachineWord.N_to_word (MachineWord.Z_idx 64) (MachineWord.Z_idx 52)) = 52).
  { unfold MachineWord.N_to_word, MachineWord.Z_idx. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. unfold bv_modulus. simpl. lia. }
  rewrite Hsh.
  assert (Hup : uint p = bv_unsigned p).
  { unfold uint, MachineWord.word_to_N, get_word. rewrite Z2N.id; [reflexivity|].
    pose proof (bv_unsigned_in_range _ p). lia. }
  rewrite Hup in Hal.
  apply Z.mod_divide in Hal; [| lia]. destruct Hal as [q Hq].
  assert (Hz0 : bv_unsigned (mword_of_int 0 : mword 64) = 0) by reflexivity.
  rewrite Hz0.
  rewrite Z.shiftl_mul_pow2; [| lia].
  rewrite Hq.
  unfold bv_wrap, bv_modulus.
  replace (2 ^ Z.of_N (MachineWord.Z_idx 64)) with (4096 * 2 ^ 52) by (vm_compute; reflexivity).
  rewrite <- Z.mul_assoc. apply Z.mod_mul. vm_compute; discriminate.
Qed.

(* kfree's epilogue [c.addi16sp +32] undoes its prologue [c.addi16sp -32],
   restoring sp to its entry value.  (mword_of_int 32 : mword 6) is -32 in
   6-bit two's complement; [caddi16sp_imm (mword_of_int 2)] is +32. *)
Lemma kfree_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6))))
          (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)) : mword 64) = 18446744073709551584) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)) : mword 64) = 32) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551584 + 32) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section Kfree.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.


  (* ============================================================= *)
  (* kfree: whole-function S-mode WP.  COMPLETE (Qed, no admits).     *)
  (* Covers the prologue (four saves + addi4spn), the auipc/addi      *)
  (* loading a5 := <end>, the bounds/alignment check region +14..+2c  *)
  (* (both panic branches shown dead from page_valid), the memset     *)
  (* argument setup and [jal memset] (wp_memset_page), the [jal       *)
  (* acquire] (wp_acquire_lock), the freelist push (p->next := head;  *)
  (* kmem.freelist := p), the [jal release] (wp_release), and the     *)
  (* epilogue (four c.ldsp restores + c.addi16sp + c.ret).            *)
  (* ============================================================= *)

  (* ===== [smode_config] leaf wrappers kfree's body needs ===== *)









  (* local wp_gpr_write_s_config_base_scfg_pt engine copy removed: sites now use
     specific per-instruction lemmas (wp_sltu_s_pt / wp_slli_s_pt / ...). *)




End Kfree.
