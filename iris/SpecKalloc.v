(* SpecKalloc.v -- the public interface of Kalloc, stated independently of its
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


Definition wp_kalloc_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (fl : mword 64) (m : regfile) (on : option nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kalloc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  (14 <= K)%nat ->
  fl = mword_of_int (KernelSyms.kmem + 24) ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* THE FRESHNESS PREMISE: kalloc acquires and releases [kmem.lock]
     internally (balanced -- [lks] is unchanged across the whole call), so
     the caller must already hold only locks BELOW "kmem"'s rank. *)
  locks_below lks "kmem" ->
  sie_cap_gpr m K b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl (mword_of_int KernelSyms.kmem) "kmem"%string (kmem_res γk fl) -∗
  kalloc_avail γk on -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    cpu_own n eb p C b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    kalloc_post γk on (mr !!! Regidx (mword_of_int 10 : mword 5)) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KALLOC.
  Parameter wp_kalloc_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (γk : gname * gname) (fl : mword 64) (m : regfile) (on : option nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (K : nat) (b : bool) (lks : gset string),
      wp_kalloc_sconf_body γl γk fl m on n eb p C K b lks.
End KALLOC.
