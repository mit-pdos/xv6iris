(* SpecAcquire.v -- the public interface of Acquire, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   The lock's [cpu] word is owned by the lock invariant (WpLock.v), so no cell
   is threaded here.  What the caller gets back is the [locked γl cpu_id]
   token, which PINS [lk->cpu] at this hart's [struct cpu] -- so release needs
   nothing else.

   A caller does NOT have to prove it is not already holding the lock: it
   supplies [panic_wp] (SpecPanic.v) instead, and acquire's
   [if(holding(lk)) panic] arm is discharged by that contract.  So the spec
   reads "acquire either returns holding the lock, or panics" -- exactly what
   the C code promises for a hart that violates the no-reentrance rule. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
From Stdlib Require Import FunctionalExtensionality.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import SpecPanic.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation AQ := KernelSyms.acquire.

(* The generic form, over [lock_openable] (WpLock.v): the right to TOUCH the
   lock is the resource [Tc], presented on the way in and handed back on the
   way out -- for a kalloc'd object that is a REFERENCE to it, which is what
   makes the storage reclaimable (a hart with no reference cannot even take
   the lock).  acquire opens the invariant four times; the first three present
   [Tc] and the last presents the [locked_pre] token it has just won, so the
   caller owes a refutation of the dead state [Dc] for each.  acquire disposes
   of nothing, so [Dc] merely rides along.  A static kernel lock instantiates
   at [Dc := False] ([wp_acquire_sconf_body] below). *)
Definition wp_acquire_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  (⊢ Tc -∗ Dc -∗ False) ->
  (⊢ locked_pre γl cpu_id -∗ Dc -∗ False) ->
  sie_cap_gpr m av b -∗
  cpu_own n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lk0 R Dc -∗
  Tc -∗
  panic_wp -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    Tc -∗
    (* [false], NOT [b]: acquire is UNBALANCED -- it opens with push_off(),
       which disables interrupts regardless of the entry state, and returns
       still holding the lock.  The [wp_next] index stays [b] (a trap CAN land
       on acquire's first instruction, before it disables), which is exactly
       the resource-index / wp_next-index divergence documented in the porting
       guide.  Threading [b] out made release -- whose entry is [false] --
       uncallable. *)
    sie_cap_gpr mfin av false -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mfin ⌝ -∗
    locked γl cpu_id -∗ R -∗
    cpu_own (S n) eb p C -∗
    trap_csrs_pay n eb -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_acquire_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  sie_cap_gpr m av b -∗
  cpu_own n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk0 s R -∗
  panic_wp -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    (* [false], NOT [b]: acquire is UNBALANCED -- it opens with push_off(),
       which disables interrupts regardless of the entry state, and returns
       still holding the lock.  The [wp_next] index stays [b] (a trap CAN land
       on acquire's first instruction, before it disables), which is exactly
       the resource-index / wp_next-index divergence documented in the porting
       guide.  Threading [b] out made release -- whose entry is [false] --
       uncallable. *)
    sie_cap_gpr mfin av false -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mfin ⌝ -∗
    locked γl cpu_id -∗ R -∗
    cpu_own (S n) eb p C -∗
    trap_csrs_pay n eb -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ACQUIRE_GEN.
  Parameter wp_acquire_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) (b : bool),
      wp_acquire_gen_sconf_body Φ γl R Tc Dc m n eb p C av b.
End ACQUIRE_GEN.

Module Type ACQUIRE.
  Parameter wp_acquire_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) (b : bool),
      wp_acquire_sconf_body Φ γl s R m n eb p C av b.
End ACQUIRE.
