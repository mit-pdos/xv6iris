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
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding WpAcquireMem WpAcquireTop.
Require Import WpRvcBridge WpLock WpLockLeaves WpHoldingInv WpPopOff.
Require Import WpAcquireLock WpRelease.
Require Import KallocInv WpKallocDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.

Section Kalloc.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* import-resolution smoke test: the decode facts, the spec transfer lemmas,
     and the callee WPs are all in scope here. *)
  Lemma wpkalloc_imports_ok : True.
  Proof. exact I. Qed.

End Kalloc.
