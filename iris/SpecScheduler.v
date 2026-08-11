(* SpecScheduler.v -- the public interface of Scheduler, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   scheduler() is the per-CPU dispatch loop and NEVER RETURNS, so this spec
   has no continuation: the conclusion is a bare [WP Loop {{Φ}}].  It is
   entered (from main, at boot) at interrupt level noff = 0 with interrupts
   DISABLED ([cpu_own γ 0 false ...]) and the spare half of [c->proc] in
   hand; the entry value of c->proc is
   irrelevant (∀ p0 -- the first thing the body does is store 0 there), and
   the cpu context slot holds the raw 14-word save area ([cpu_ctx_free], the
   boot shape) -- the scheduler is the party that parks itself there.

   Interrupt accounting (see claude-notes/projects/scheduler.md): the loop
   head's inlined intr_on/intr_off ([csrsi]/[csrci sstatus,2]) flip the SIE
   arm at level 0, which consumes [trap_csrs] (the ∃-valued sepc/scause/stval
   cells -- a taken trap scribbles them, so the enabled arm must own them)
   and the persistent [intr_handler_avail γ] (trapinithart has installed
   kernelvec).  A dispatch round can hand the scan back at eb = true (the
   parked proc's release re-enables), so both are genuinely consumed and
   re-emerge round by round; the spec takes them once, at the boot shape
   (interrupts off, cells client-side).

   The scheduler is the supplier of the chain's dispatch payload and the
   consumer of its parking payload (SchedCtx.p_sched); [procs_inv] provides
   the 64 proc locks, and [panic_wp] discharges acquire's holding-panic arm. *)
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
Require Import KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_scheduler_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (m : regfile) (av : nat) (p0 : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.scheduler in
  (* scheduler() runs with NO current proc -- that is the fact [wp_next_idle]
     turns into "the scheduler thread cannot migrate".  So the index is the
     literal zero, not a binder. *)
  p0 = zero_reg ->
  (* [kv_frame_slots + 20], NOT [20] -- ONE reserve, paid ONCE.
     scheduler() is entered from main() with interrupts OFF, and the [intr_on]
     inlined at its loop head ([csrsi sstatus,2] at +0x86) is therefore a
     genuine 0 -> 1 enable at a point where NOBODY holds the trap reserve: it
     has to fund [kv_frame_slots] out of the scheduler's own budget, exactly
     like sleep's re-enabling release.  It is funded once and for all: on
     every later round the arm is already [true] (the dispatch tail's release
     at level 0 with [intena] re-enabled it), the same [csrsi] is an
     IDEMPOTENT set that moves neither ghost state nor the index
     ([WpSconfCsr.wp_csrsi_sstatus_x0_idem_s_sconf]), and the reserve carved
     on the first round is simply still there.  So the premise is
     [kv_frame_slots + <loop body need>] with NO factor of two -- carrying the
     arm-generic enable leaf around the loop instead would demand room to set
     aside [kv_frame_slots] in a state where they are ALREADY set aside, i.e.
     [2 * kv_frame_slots + 20], which is the pathology the arm-dependent carve
     exists to remove. *)
  (kv_frame_slots + 20 <= av)%nat ->
  sie_cap_gpr m av false p0 -∗
  cpu_own 0 false p0 cpu_ctx_free false -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  (* HART-GENERIC.  scheduler() never migrates -- that is what [wp_next_idle]
     and its [p = zero_reg] hatch express -- but that is not the point: the
     [acquire] it calls in the scan asks for [panic_wp_any], a resource
     quantified over EVERY hart, and one hart's copy does not yield it.  Same
     propagation as SpecMain / SpecKinit / SpecUserinit / kalloc_env. *)
  panic_wp_any -∗
  trap_csrs -∗
  intr_handler_avail -∗
  WP (Loop : expr riscv_lang).

Module Type SCHEDULER.
  Parameter wp_scheduler_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (m : regfile) (av : nat) (p0 : mword 64),
      wp_scheduler_sconf_body γs m av p0.
End SCHEDULER.
