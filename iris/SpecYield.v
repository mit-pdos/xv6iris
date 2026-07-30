(* SpecYield.v -- the public interface of Yield, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   yield() gives up the CPU: from a normally-running kernel thread (no locks
   held, noff = 0, interrupts enabled at the base -- [eb = true], which is
   what makes the trap-CSR exchange across the park balanced; this CPU's
   current process is proc j, the scheduler parked under ▷), it acquires
   p->lock, marks the process RUNNABLE, parks through sched(), and -- once
   some scheduler dispatches the process again -- releases the lock and
   returns.

   IT RETURNS ON THE HART THAT DISPATCHED IT, not necessarily the one it
   parked from (SpecSched.v): the continuation is quantified over that hart
   [h] and its SIE ghost [g], every resource comes back at [(h, g)], and the
   register fact is [callee_saved_notp m mf] plus [mf !!! x4 = cid_word_of h]
   (CalleeSaved.v).  The trap CSRs never appear: yield's own acquire takes
   them and its own release gives them back, and the crossing in between
   carries them inside the chain payload.

   The context slot [C] stays ONE hart-independent proposition, carried out of
   the entry bundle and back into the exit bundle unchanged.  A hart-INDEXED
   slot [C : CPU -> iProp Σ] is not provable here and never could be: nothing
   in the crossing can turn [C cpu_id] into [C h], so such a spec would need a
   hart-transport bridge as an extra premise -- and a [C] that admits one is
   exactly a hart-independent [C].  (Every real instantiation is [emp]: a
   running thread's parked-scheduler obligation rides the separate
   [▷ sched_vc] premise, not the slot.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SwtchCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation YD := KernelSyms.yield.

Definition wp_yield_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.yield in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  eb = true ->
  (20 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ 0 eb pj C -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv Φ γs -∗
  panic_wp -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) pj -∗
  ( ∀ (h : CPU) (g : gname) (mf : regfile),
      ⌜callee_saved_notp m mf⌝ -∗
      ⌜mf !!! Regidx (mword_of_int 4 : mword 5) = cid_word_of h⌝ -∗
      sie_cap_gpr (CID := h) g mf av -∗
      cpu_own (CID := h) g 0 eb pj C -∗
      pc_is (CID := h) ret_tgt -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc_at Φ γs h g (a_cpu_ctx (cid_word_of h)) pj -∗
      WP (LoopE h : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type YIELD.
  Parameter wp_yield_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ),
      wp_yield_sconf_body γ Φ γs j γl m av eb C.
End YIELD.
