(* SpecKfree.v -- the public interface of Kfree, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KallocInv.
Require Import WpLock.
Require Import IntrDefs.
Require Import PanicStub.
Require Import CpuOwn.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.


Definition wp_kfree_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (on : option nat) (n : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kfree in
  let p := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (14 <= K)%nat ->
  lk = mword_of_int KernelSyms.kmem ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* THE FRESHNESS PREMISE: kfree acquires and releases [kmem.lock]
     internally (balanced -- [lks] is unchanged across the whole call), so
     the caller must already hold only locks BELOW "kmem"'s rank. *)
  locks_below lks "kmem" ->
  sie_cap_gpr m K b pcur -∗
  cpu_own n eb pcur C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk "kmem"%string (kmem_res γk fl) -∗
  kfree_pre p -∗
  kalloc_avail γk on -∗
  panic_wp_any -∗
  wp_next b pcur (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b pcur -∗
    cpu_own n eb pcur C b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_avail γk (avail_inc on) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KFREE.
  Parameter wp_kfree_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (lk fl : mword 64) (m : regfile) (on : option nat) (n : nat) (eb : bool) (pcur : mword 64) (C : iProp Σ) (K : nat) (b : bool) (lks : gset string),
      wp_kfree_sconf_body γl γk lk fl m on n eb pcur C K b lks.
End KFREE.
