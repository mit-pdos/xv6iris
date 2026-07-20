(* WpHoldingInv.v -- holding() against the CSL lock invariant: the lock-word
   read at +0x0 goes THROUGH [is_lock] (WpLockLeaves.wp_clw_lockinv_pt and twin), so the
   caller owns no lock-word bytes.  Two flavors:

     wp_holding_lockinv         -- caller does NOT hold the lock (its cpu
                                   field differs from mycpu()): holding()
                                   returns 0 on both the fast (word 0) and
                                   slow (word nonzero) paths.
     wp_holding_lockinv_locked  -- caller HOLDS [locked γ] and lk->cpu is
                                   mycpu(): the invariant's free branch is
                                   refuted at the read, so the slow path is
                                   taken and holding() returns 1.

   Both are built from WpHolding.v's decode/leaf lemmas (hi_00..hi_06,
   his_08..his_2a), with instruction +0x0 swapped for the invariant-mediated
   read. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SRegime.
Require Import SmodeCore.
Require Import WpMycpu.
Require Import KernelRvcDecode.
Require Import CalleeSaved StackOwn.
Require Import WpHolding WpLock.
Require Export WpSmodeLeafBase.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import KptTree.
Require Import WpSmodePtLeaves WpSmodePtAlu WpSmodePtBtype WpSmodePtCtl.
Require Import WpSmodePtMemWrap WpSmodePtLock.
Import Defs.

(* seqz on a-b for EQUAL operands: result 1 (twin of WpHolding.seqz_sub_neq) *)
Lemma seqz_sub_eq (a b : mword 64) :
  eq_vec a b = true ->
  zero_extend' 64 (bool_to_bit (zopz0zI_u (sub_vec a b)
    (sign_extend' 64 (mword_of_int 1 : mword 12)))) = (mword_of_int 1 : mword 64).
Proof.
  intro He.
  assert (Hab : a = b) by (apply eq_vec_true_iff; exact He).
  subst b.
  replace (sub_vec a a) with (zeros' 64 : mword 64);
    [ apply bv_eq; vm_compute; reflexivity | ].
  apply bv_eq.
  unfold sub_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.sub.
  rewrite bv_sub_unsigned. rewrite Z.sub_diag. reflexivity.
Qed.

Section WpHoldingInv.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ---- [smode_config] leaf wrappers for holding.  All config-preserving
     (holding never touches mstatus), so each just unbundles → raw leaf →
     rebundles.  The sstatus-reading leaves (cret/cbnez_fall/cbnez_taken_zca…)
     reuse the wrappers exported by WpPopOff. ---- *)























End WpHoldingInv.
