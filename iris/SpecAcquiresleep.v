(* SpecAcquiresleep.v -- the public interface of Acquiresleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The separation-logic lock spec, sleeplock flavour:

     { is_sleeplock γl γ slk s R ∗ <thread resources> }
       acquiresleep(slk)
     { sleeplocked γ ∗ sl_pid slk ↦₄ pid ∗ R ∗ <thread resources> }

   The <thread resources> are what the body's callees demand: the per-cpu
   push_off cells and the inner lock's cpu word (acquire/release), the
   current-process resource and the caller's own pid cell at a read
   fraction (lk->pid = myproc()->pid), and -- because the wait loop parks
   through sleep() -- the running-thread bundle of the scheduler protocol
   (SpecSleep.v).  Entered with no spinlocks held (intr_count 0, noff cell
   0): sleep() requires exactly one level outstanding, which forces it. *)
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
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_acquiresleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  panic_wp_any -∗
  (* the caller's own pid (read-only fraction) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through to sleep() *)
  procs_inv γs -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      (* the lock is now HELD: token + pid field + protected resource *)
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  ROUTE B, LEMMA (3): THE NESTED acquiresleep.                          *)
(* ===================================================================== *)
(* iput calls acquiresleep(&ip->lock) while HOLDING itable.lock -- the
   kernel's only nested acquiresleep (fs.c:348).  The contract above is
   unusable there: it demands [cpu_own 0], because everything below it
   sleeps.  Design fs-icache.md 13.12 adopts Route B: the LOCKED branch
   runs sleep() at noff >= 2, which reaches sched's panic("sched locks")
   and DIVERGES ([SpecSleep.wp_sleep_locks_body]); the FREE branch takes
   the lock and returns.  So the nested contract is the ordinary one with

     - the level raised to [S n] and the resource index pinned to the
       LITERAL [false] ([cpu_own]'s enabled arm demands noff = 0, so a
       [b] binder would have exactly one live instance anyway);
     - NO [eb = true] parking premise.  It exists so a parking thread can
       hand the trap CSRs across a swtch; the returning branch never
       parks and the other branch has no postcondition;
     - the crossing index [false] as well: the caller is inside its own
       critical section, so no leaf here can move the hart.

   The postcondition is otherwise IDENTICAL -- [sleeplocked], the pid
   cell, the protected [R] -- and the level comes back unchanged, i.e.
   the function is noff-balanced exactly as at level 0.

   REF-1 (design 5(b)) makes the divergence unreachable at iput's call
   site; we do not prove that, we permit it.                             *)
Definition wp_acquiresleep_nested_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac)
    (n : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  (* the interior acquire pushes to [S (S n)] and sleep's own acquire to
     [S (S (S n))], transiently +1 *)
  (Z.of_nat n + 4 < 2 ^ 31)%Z ->
  sie_cap_gpr m av false pj -∗
  (* NESTED: a spinlock IS held on entry, and is still held on exit *)
  cpu_own (S n) eb pj C false -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  panic_wp_any -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  wp_next false pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av false pj -∗
      cpu_own (S n) eb pj C false -∗
      pc_is ret_tgt -∗
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ACQUIRESLEEP.
  Parameter wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac} (b : bool),
      wp_acquiresleep_sconf_body γs j γl γsl s R m pidv av eb C dq b.
  Parameter wp_acquiresleep_nested_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac}
      (n : nat),
      wp_acquiresleep_nested_body γs j γl γsl s R m pidv av eb C dq n.
End ACQUIRESLEEP.
