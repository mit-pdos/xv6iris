(* SpecKilled.v -- the public interface of killed(), stated independently of
   its proof.

     int killed(struct proc *p) {
       int k;
       acquire(&p->lock);
       k = p->killed;
       release(&p->lock);
       return k;
     }

   @ KernelSyms.killed = 0x80002142, nineteen instructions: a 32-byte
   ra/s0/s1/s2 frame, [c.mv s1,a0] to park [p] across the calls,
   acquire, [c.lw a5,40(s1)] (p->killed), [c.mv s2,a5] to park the value
   across release, release, [c.mv a0,s2].

   THE POINT.  This is the first consumer of the always-resident row of the
   proc lock invariant: [p_killed] lives in [SchedCtx.proc_pub], at the TOP
   LEVEL of [proc_lock_res], so killed() reaches it by opening the lock and
   destructing one existential -- it never learns the process's state and
   never touches either of the two [proc_slots] guards.  Before that rewiring
   the field was not modelled at all.

   The returned value is universally quantified in the continuation: the
   invariant says nothing about [p->killed], so a caller must accept whatever
   it reads (the same shape as sys_uptime's tick value).  It is
   [sign_extend' 64 kl] because [c.lw] is a signed 32-bit load widening to
   the [int] return type.

   [panic_wp] is threaded because acquire takes it (its "acquire" panic on a
   doubly-held lock). *)
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
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import SchedCtx.
Require Import PanicStub.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_killed_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
     (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.killed in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the argument is proc j *)
  m !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for acquire's / release's *)
  (14 <= av)%nat ->
  (* THE FRESHNESS PREMISE: killed acquires and releases [p->lock]
     internally (balanced -- [lks] is unchanged across the whole call), so
     the caller must already hold only locks BELOW "proc"'s rank. *)
  locks_below lks "proc" ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (kl : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = sign_extend' 64 kl ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b lks -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KILLED.
  Parameter wp_killed_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string),
      wp_killed_sconf_body γs j γl m av n eb p C b lks.
End KILLED.
