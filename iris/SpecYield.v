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
   register fact is [callee_saved m mf] (tp-free) plus <the tp conjunct, now deleted: tp_pin makes it true by construction>
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
Require Import WpNext.
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


Definition wp_yield_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.yield in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  eb = true ->
  (20 <= av)%nat ->
  sie_cap_gpr m av b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  panic_wp_any -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type YIELD.
  Parameter wp_yield_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_yield_sconf_body Φ γs j γl m av eb C b.
End YIELD.
