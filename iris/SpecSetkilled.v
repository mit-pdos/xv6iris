(* SpecSetkilled.v -- the public interface of setkilled(), stated
   independently of its proof.

     void setkilled(struct proc *p) {
       acquire(&p->lock);
       p->killed = 1;
       release(&p->lock);
     }

   @ KernelSyms.setkilled = 0x8000211e, sixteen instructions: a 32-byte
   ra/s0/s1 frame (slot 0 is padding), [c.mv s1,a0] to park [p] across the
   two calls, acquire, [c.li a5,1] + [c.sw a5,40(s1)] (p->killed = 1),
   [c.mv a0,s1], release.

   THE POINT, and the reason the postcondition is EMPTY.  [p_killed] lives
   in [SchedCtx.proc_pub], at the TOP LEVEL of [proc_lock_res] -- but
   [proc_pub] quantifies the flag EXISTENTIALLY, so the invariant says
   nothing about its value and there is nothing for a caller to learn.
   setkilled is therefore the mirror image of killed(): killed() reads a
   value the contract cannot constrain, setkilled writes one the contract
   need not report.  Both reach the cell by opening the lock and destructing
   one existential, and neither ever learns the process's state or touches
   either [proc_slots] guard -- which is exactly what the invariant's
   always-resident row is for.

   Making the write visible would mean giving [p->killed] a fraction that
   travels with the running thread (the [pid] discipline), and no consumer
   wants one: the only reader is killed(), which any hart may call on any
   proc.  See claude-notes/design/proc-struct.md, discipline 1.

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


Definition wp_setkilled_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
     (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.setkilled in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the argument is proc j *)
  m !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for acquire's / release's *)
  (14 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b lks -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SETKILLED.
  Parameter wp_setkilled_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset nat),
      wp_setkilled_sconf_body γs j γl m av n eb p C b lks.
End SETKILLED.
