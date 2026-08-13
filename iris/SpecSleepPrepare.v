(* SpecSleepPrepare.v -- the public interface of sleep_prepare(), stated
   independently of its proof.

     void sleep_prepare(void *chan) {
       struct proc *p = myproc();
       acquire(&p->lock);
       if (chan == 0) panic("sleep_prepare: zero chan");
       p->chan = chan;
       release(&p->lock);
     }

   THE FIRST HALF OF THE SPLIT SLEEP PROTOCOL (SpecSleep.v's header has the
   whole picture).  A thread that wants to wait registers its channel HERE,
   while still holding its condition lock, then drops that lock and calls
   sleep().  The register is what closes the missed-wakeup window: wakeup()
   CLEARS [p->chan] rather than only moving SLEEPING processes, so a wakeup
   landing in between makes the later sleep() a no-op.

   THE POSTCONDITION IS EMPTY, for setkilled()'s reason: [p_chan] lives at
   the top level of [SchedCtx.proc_lock_res], but the invariant quantifies
   its value EXISTENTIALLY, so the write is invisible and there is nothing
   for a caller to learn.  That is exactly right here -- the value only ever
   matters to sleep() and wakeup(), which read it under the same lock, and
   the two of them agree through the invariant rather than through any
   caller's hands.  (Making the write visible would mean giving [p->chan] a
   fraction that travels with the running thread; no consumer wants one, and
   one would have to survive a park, where the thread owns nothing.)

   [chan <> 0] IS A PREMISE because the zero case panics.  Every call site
   in the kernel passes the address of a static or of a live object, so the
   premise is free; refuting the panic arm rather than proving it is what
   keeps [printk] out of this cone.

   ENTERED WITH THE CONDITION LOCK HELD, hence at level [n] rather than 0,
   and [b]/[eb]-generic like setkilled(): sleep_prepare neither parks nor
   changes the interrupt discipline, so it is noff-balanced and its
   [wp_next] index is the caller's own [b].  WHICH PROC IT REGISTERS is read
   out of [cpu_own]'s c->proc cell by the interior myproc() -- so, unlike
   setkilled(), the proc is not an argument and the contract pins the
   running process to [proc_addr j]. *)
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
Require Import SchedCtx.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sleep_prepare_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep_prepare in
  let pj := proc_addr j in
  (* a0 = the channel *)
  let chan : mword 64 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (* the panic arm, refuted *)
  eq_vec chan (zero_reg : mword 64) = false ->
  (* the interior acquire's push_off keeps the transient increment in range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for myproc's / acquire's / release's *)
  (14 <= av)%nat ->
  sie_cap_gpr m av b pj -∗
  cpu_own n eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own n eb pj C b -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SLEEP_PREPARE.
  Parameter wp_sleep_prepare_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_sleep_prepare_sconf_body γs j γl m av n eb C b.
End SLEEP_PREPARE.
