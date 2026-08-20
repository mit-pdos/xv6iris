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

   The panic credentials are threaded because acquire takes them (its
   "acquire" panic on a doubly-held lock). *)
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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpNext.
Require Import LockRank.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import SchedCtx.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Definition wp_setkilled_sconf_body `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
     (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.setkilled in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the argument is proc j *)
  m !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j ->
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for acquire's / release's *)
  (14 <= av)%nat ->
  (* THE ORDER PREMISE for the one lock this function takes: everything the
     caller already holds ranks strictly BELOW "proc".  It composes across a
     call chain in a way the bare non-membership does not
     ([LockRank.locks_below_mono]), and [locks_below_not_elem] recovers the
     ["proc" ∉ lks] the ghost step and the set algebra below need.
     No execution ever holds two "proc" locks at once (LockRank.v), so a
     caller inside some OTHER proc's critical section is not a problem here.
     setkilled is BALANCED -- both the entry and the exit [cpu_own] carry the
     same [lks] -- because the C releases p->lock on its only return path. *)
  locks_below lks "proc" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SETKILLED.
  Parameter wp_setkilled_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !fileG Σ} `{GEN : GenId} `{CID : CpuId}
       (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (b : bool) (lks : gset string),
      wp_setkilled_sconf_body γs j γl m av n eb p b lks.
End SETKILLED.
