(* SpecYield.v -- the public interface of Yield, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   yield() gives up the CPU: from a normally-running kernel thread (no locks
   held, noff = 0, saved base enable [eb] ARBITRARY; this CPU's current
   process is proc j, the scheduler parked under ▷), it acquires
   p->lock, marks the process RUNNABLE, parks through sched(), and -- once
   some scheduler dispatches the process again -- releases the lock and
   returns.

   IT RETURNS ON THE HART THAT DISPATCHED IT, not necessarily the one it
   parked from (SpecSched.v): the continuation is quantified over that hart
   [h] and its SIE ghost [g], every resource comes back at [(h, g)], and the
   register fact is [callee_saved m mf] (tp-free) plus <the tp conjunct, now deleted: tp_pin makes it true by construction>
   (CalleeSaved.v).  ONE INDEX, NOT TWO.  [eb] (the saved base
   enable) and the resource index used to be separate binders; at level 0
   they are the same bit, forced by ghost agreement between [sie_arm]'s
   eighth and [intr_count 0 eb]'s ([CpuOwn.cpu_own_eb_agree]), so a second
   binder only ever admitted vacuous instances.

   [eb] IS NOT PINNED.  It used to be [true], which made this contract
   unusable from kerneltrap -- the trap cleared SIE, so the acquire inside
   yield records intena = 0 and the whole call runs at [eb = false].  Both
   of yield's callers in the C (usertrap and kerneltrap) reach it that way,
   on the timer path, with no [intr_on()] in between.

   WHICH IS WHY THE TRAP CSRs ARE A PREMISE.  sched's crossing demands the
   set unconditionally, and sepc/scause/stval are PER-HART registers, so a
   parking function cannot frame them -- it must hand them over and take the
   RESUMING hart's back.  At [eb = true] yield's own acquire produces them
   (dismantling the enabled SIE arm) and [trap_csrs_ext true = emp]; at
   [eb = false] there is no arm to dismantle and the caller brings them.

   THE RAW CONTEXT CELLS ARE NOT A PREMISE.  They live in p->lock, under
   the RUNNING arm of [SchedCtx.proc_slots], and yield reads them out of the
   lock it acquires -- the park receipt half it already carries refutes the
   lock's [not_running] arm, which is the proof that the state under the
   lock IS RUNNING ([SchedCtx.proc_slots_running]).  Demanding [own_ctx] up
   front would have made this contract unusable from kerneltrap, which
   PREEMPTED the thread and so cannot be holding the thread's own frames.

   THE CROSSING INDEX IS THE LITERAL [true], as for [sched]: a parking
   function migrates whatever the SIE state was, because a [swtch] moves the
   hart with interrupts off.  Threading [eb] there would have claimed, at
   [eb = false], that yield returns on the hart that called it.

   THE RESUMING HART'S INSTALLED-HANDLER RESOURCE COMES OUT INSIDE
   [trap_csrs_ext eb], and it is what makes this contract usable from a trap
   handler at all: the one thing a returning trap must still do is [sret],
   which flips SIE from '0' to '1' and therefore needs the handler resource in
   hand.  It is PER-HART, so a caller's own copy would be about the wrong hart
   the moment yield crosses a park; sched's dispatch payload carries the
   dispatching hart's, and it now rides inside the trap-CSR bundle that was
   already crossing.

   THAT USED TO BE A SEPARATE PREMISE, [intr_handler_avail_ext eb], with its
   own transport and its own forced-[emp] arm at [eb = true].  Both are gone:
   the resource is a conjunct of [trap_csrs], so the existing
   [trap_csrs_ext] carrier and [trap_csrs_ext_transport] serve it, and at
   [eb = true] it comes back inside the returned bundle's [sie_arm true] --
   where, being owned rather than behind an invariant, it can simply be read
   out.

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
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.


Definition wp_yield_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.yield in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (20 <= av)%nat ->
  sie_cap_gpr KT1 m av eb pj -∗
  cpu_own 0 eb pj eb ∅ -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av eb pj -∗
      cpu_own 0 eb pj eb ∅ -∗
      pc_is ret_tgt -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type YIELD.
  Parameter wp_yield_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool),
      wp_yield_sconf_body γs j γl m av eb.
End YIELD.
