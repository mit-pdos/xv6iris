(* SpecKkill.v -- the public interface of kkill() (xv6's kill(), renamed in
   this tree because the model already owns the name), stated independently
   of its proof.

     int kkill(int pid) {
       for (struct proc *p = proc; p < &proc[NPROC]; p++) {
         acquire(&p->lock);
         if (p->pid == pid) {
           p->killed = 1;
           if (p->state == SLEEPING) p->state = RUNNABLE;
           release(&p->lock);
           return 0;
         }
         release(&p->lock);
       }
       return -1;
     }

   @ KernelSyms.kkill = 0x800020b8, thirty-five instructions: a 48-byte
   ra/s0/s1/s2/s3 frame (slot 0 is padding), s1 the proc[] cursor, s2 the
   [pid] argument, s3 = &proc[NPROC] (which the linker places at
   <tickslock>), acquire/release per slot, one shared release-and-return-0
   block at +0x4a reached from both arms of the SLEEPING test.

   THE POINT.  kkill is the second function -- with wakeup -- that walks
   procs it does not own, and like wakeup it reaches everything it touches
   at the TOP LEVEL of [proc_lock_res] and never opens either [proc_slots]
   guard:

     - [p->pid] is the invariant's permanent half of the cell, resident in
       [SchedCtx.proc_pub];
     - [p->killed] is resident in [proc_pub] too, and existentially
       quantified there, so the store needs no premise and reports nothing;
     - SLEEPING -> RUNNABLE keeps both guards' booleans fixed, so the
       transition is [SchedCtx.proc_lock_res_wakeup] -- literally the same
       lemma wakeup uses, which is what the flat two-boolean row was for.

   THE RESULT IS 0 OR -1 AND NOTHING MORE.  Whether some proc's [pid] cell
   matches the argument is not determined by anything the caller holds --
   [proc_pub] quantifies the pid, and no resource in the tree ties a pid to
   a slot -- so the return value is existential with that two-way
   constraint, the same honesty as sys_pause's and killed's.  Making it
   sharper would need a pid->slot ghost map that no consumer wants: the one
   caller, sys_kill, hands the value straight back to user space.

   The [pid] argument itself is unconstrained: the [beq] compares the full
   64-bit registers ([lw]'s sign-extended [p->pid] against whatever the
   caller left in a0), and since both outcomes are live the contract need
   not relate them.

   [panic_wp] is threaded because acquire takes it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
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
Require Import FdSlots FileInv.
Require Import SchedCtx.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_kkill_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
     (γs : list gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.kkill in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  length γs = NPROC ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 6 slots for this frame, 10 for acquire's / release's *)
  (16 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (rv : mword 64),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = rv /\
        (rv = (zero_reg : mword 64) \/ rv = mword_of_int (-1)) ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type KKILL.
  Parameter wp_kkill_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool),
      wp_kkill_sconf_body γs m av n eb p C b.
End KKILL.
