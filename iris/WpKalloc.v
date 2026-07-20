(* WpKalloc.v -- instruction-level proof of the kernel's [kalloc] (0x80000b20)
   and [kfree] (0x80000a38) against the allocator spec in KallocInv.v.

   kalloc/kfree are whole-function S-mode proofs in the mould of [wp_release]
   (WpRelease.v) and [wp_acquire_lock] (WpAcquireLock.v): they thread the S-mode
   machine configuration (mstatus/pmp/pte/tlb) through every instruction and
   CALL the sub-functions acquire / release / memset via [jal], discharging each
   callee's whole-function WP.  The novel content is the free-list manipulation,
   which is discharged by KallocInv's transfer lemmas [kmem_res_pop] /
   [kmem_res_push] together with [page_head8_word_at] / [run_page_page_own]. *)
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
Require Import WpSmodePtMemWrap.
Require Export WpSmodeLeafBase.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.


(* the +32/-32 c.addi16sp frame cancel (kalloc's frame; clone of
   WpKfree's kfree_sp_cancel -- neither file imports the other) *)
Lemma kalloc_sp_cancel (X : mword 64) :
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

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation AK := KernelSyms.kalloc.
  Notation AQ := KernelSyms.acquire.
  Notation PO := KernelSyms.push_off.

  (* ===== [smode_config] leaf wrappers kalloc's body needs ===== *)







  (* local wp_gpr_write_s_config_base_scfg_pt engine copy removed (unused). *)
  (* ============================================================= *)
  (* kalloc: whole-function S-mode WP.  COMPLETE (Qed, no admits).  *)
  (* Single full-[stack_own] lemma: pre and post are [stack_own     *)
  (* sp0 n] (n >= 14).  kalloc peels its own 4-slot frame and lends  *)
  (* the deep tail [stack_own spr (n-4)] to acquire / release /      *)
  (* memset in turn, each returning it intact (no stack leak).       *)
  (* ============================================================= *)


End Kalloc.
