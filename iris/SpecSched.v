(* SpecSched.v -- the public interface of Sched, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   sched() parks the current process: entered holding EXACTLY p->lock
   (noff == 1, interrupts off, saved base enable [eb] ARBITRARY -- see the
   premise block below; a thread parked from kerneltrap has [eb = false]),
   with the
   process's state already moved to a parked state (yield sets RUNNABLE,
   sleep sets SLEEPING -- [needs_ctx st]).  It swtches into this CPU's
   scheduler context, handing over the held lock, the state/chan cells, the
   trap CSRs and the per-CPU cells (the p_sched chain payload, SchedCtx.v).

   IT DOES NOT RETURN ON THE HART IT PARKED FROM.  Proc contexts are
   MIGRATABLE ([ctx_adm = None], SwtchCtx.v): any hart's scheduler may
   dispatch this process, swtch does not save tp, and the resumed thread
   inherits the resuming hart's.  So the continuation is wrapped in
   [wp_next b], whose rebound [CID] IS the resuming hart -- every resource
   it receives resolves at that hart automatically (no [(CID := h)]
   annotation, no separate ghost-name binder: the SIE ghost is canonical per
   hart now), and its conclusion is the plain [WP (Loop)] at the rebound
   [CID].  sched always swtches (there is no non-parking path), so the proof
   establishes the fully hart-generic postcondition regardless of [b] and
   discharges the wrapper via [wp_next_intro] for whichever index a caller
   supplies; sched's OWN [sie_cap_gpr]/[cpu_own] resource index stays the
   literal [false] throughout (entered at noff == 1, and [cpu_own]'s
   [b = true] arm demands noff == 0) -- a second, DISTINCT index from
   [wp_next]'s own [b] (see explicit-cpuid-porting-guide.md, "two different
   indices").  The register postcondition weakens to [callee_saved m mf]
   (CalleeSaved.v's tp-free relation); the old <the tp conjunct, now deleted: tp_pin makes it true by construction>
   conjunct is gone -- [tp_pin] makes it true by construction.

   What the continuation gets back: same j, state now RUNNING, lock held on
   the resumed hart, the trap CSRs and that hart's fresh
   [intr_handler_avail] (the dispatch payload's, which is what a caller's
   own release/retune needs under the fresh ghost), c->proc back at proc j,
   and a FRESH parked scheduler context under ▷ ([sched_vc], which resolves
   at the rebound hart the same way). *)
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
Require Import IntrDefs HartTp WpNext.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sched_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
    (m : regfile) (av : nat) (eb : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sched in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* THE PARKED STATE.  Its caller has already stored it: yield RUNNABLE,
     sleep SLEEPING, kexit ZOMBIE.  [park_ok] rather than [needs_ctx]
     (ProcGeom.v) because the third one never comes back -- see the
     [park_pay] premise below, and SchedCtx's [proc_slots_park_gen]. *)
  park_ok st = true ->
  (* NO CONSTRAINT ON [eb].  It used to be pinned [true], on the reasoning
     that a parked kernel thread always got here from interrupts-enabled
     code -- which is FALSE of a thread parked from kerneltrap: that one got
     here from a TRAP, so the pushing acquire recorded intena = 0.  The
     premise was never used by the proof either (it was introduced and
     dropped), because nothing here depends on the value: the trap CSRs are
     threaded EXPLICITLY below rather than taken out of the SIE arm, and the
     post-swtch intena restore + ghost retune already run at both values
     ([intr_count_retune_on] / [_off]).  [intr_handler_avail] in the
     postcondition is likewise value-independent: it comes from the DISPATCH
     payload -- the scheduler that resumes this thread always runs with
     interrupts on -- not from this thread's own entry stash. *)
  (16 <= av)%nat ->
  (* TWO INDICES, AND THEY ARE OPPOSITE CONSTANTS.  sched is entered holding
     p->lock at noff == 1, so its OWN resource index is pinned [false]
     (cpu_own's [b = true] arm demands [n = 0], which would make the whole
     premise [False] -- a vacuous instance, not a usable one).  Its crossing
     index is the literal [true]: a PARKING function's [wp_next] index is
     [true] UNCONDITIONALLY, because a [swtch] moves the hart with interrupts
     OFF and so has nothing to do with SIE.  Threading one [b] through both
     slots claimed, at the only live instance, that sched returns on the hart
     that called it -- which is false twice over ([SpecSwtch]'s continuation
     is over an arbitrary hart, and the post-resume release exits at
     [outb = eb = true]).  There is consequently no [b] binder left. *)
  sie_cap_gpr m av false pj -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  proc_held cpu_id j γl st ch -∗
  (* WHAT THE PARKED SLOT OWES BESIDES THE SAVED CONTEXT (SchedCtx.park_pay):
     [emp] at a resumable park -- the private block stays in the parking
     thread's own closure -- and, at the ZOMBIE park, the dormant block minus
     its context cells, because nothing will ever resume the closure and
     wait()/freeproc must find that block in the lock. *)
  park_pay pj st -∗
  (* handed over at the crossing, taken back from the dispatch payload. *)
  trap_csrs -∗
  (* the cpu bundle at level 1 (xv6 asserts noff==1 at sched), slot [emp]:
     the parked-scheduler slot content is the ▷ sched_vc premise below.
     sched PRESERVES [eb] across the park -- its intena save/restore is
     exactly the eb retune back to the caller's own state, now realized
     against the DISPATCHING hart's fresh [intr_handler_avail] (the entry
     stash is about the wrong hart's ghost). *)
  cpu_own 1 eb pj emp false -∗
  own_ctx (p_context pj) -∗
  (* THE HART TAG, WHOLE.  The parking thread merged the slot's half with its
     own claim's half at [SchedCtx.proc_slots_running], and the reclaiming
     scheduler needs the whole tag to close the parked slot's [not_running]
     guard.  It comes back whole on the dispatch side, at the RESUMING hart,
     which is what lets the resumed thread rebuild [run_slot] and its own
     [cpu_claim] out of one resource. *)
  hart_full j cpu_id -∗
  ▷ sched_vc γs (a_cpu_ctx cid_word) pj -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (ch' : mword 64),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av false pj -∗
      pc_is ret_tgt -∗
      proc_held cpu_id j γl RUNNING ch' -∗
      trap_csrs -∗
      intr_handler_avail -∗
      cpu_own 1 eb pj emp false -∗
      own_ctx (p_context pj) -∗
      hart_full j cpu_id -∗
      ▷ sched_vc γs (a_cpu_ctx cid_word) pj -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SCHED.
  Parameter wp_sched_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      
      (γs : list gname) (j : nat) (γl : gname) (st : mword 32) (ch : mword 64)
      (m : regfile) (av : nat) (eb : bool),
      wp_sched_sconf_body γs j γl st ch m av eb.
End SCHED.
