(* SpecScheduler.v -- the public interface of Scheduler, stated independently
   of its proof.  Requires only the definitional layer -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   scheduler() is the per-CPU dispatch loop and NEVER RETURNS, so this spec
   has no continuation: the conclusion is a bare [WP Loop {{Φ}}].  It is
   entered (from main, at boot) at interrupt level noff = 0 with interrupts
   DISABLED ([cpu_own γ 0 false ...]); the entry value of c->proc is
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
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SC := KernelSyms.scheduler.

Definition wp_scheduler_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (m : regfile) (av : nat) (p0 : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.scheduler in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (20 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ 0 false p0 cpu_ctx_free -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γ Φ γs -∗
  panic_wp -∗
  trap_csrs -∗
  intr_handler_avail γ -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SCHEDULER.
  Parameter wp_scheduler_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (m : regfile) (av : nat) (p0 : mword 64),
      wp_scheduler_sconf_body γ Φ γs m av p0.
End SCHEDULER.
