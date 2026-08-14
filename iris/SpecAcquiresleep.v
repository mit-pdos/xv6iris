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
Require Import PanicStub.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_acquiresleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac) (b : bool) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  (* acquiresleep's own acquire(&slk->lk) needs every lock this hart
     already holds to rank below "sleep lock".  The RAW spinlock is
     released again before this function returns (the sleeplock's
     higher-level "locked" state is a separate ghost token, [sleeplocked],
     untouched by [lks]), so [lks] itself is unchanged end to end. *)
  locks_below lks (lock_rank "sleep lock") ->
  sie_cap_gpr m av b pj -∗
  cpu_own 0 eb pj C b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM.  Everything below sleeps,
     and a parking thread must hand [trap_csrs] and [cpu_claim] across the
     crossing (SpecSched.v).  At [eb = true] acquiresleep's OWN acquire frees
     them out of [sie_arm true], so the complement is [emp] and the caller
     brings nothing -- which is why this used to be an [eb = true] premise
     instead.  At [eb = false] the push_off frees nothing and the caller
     brings the pair, holding it because the TRAP handed it over; that is the
     case iput/ilock need, and through them kexit and usertrap. *)
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  panic_wp_any -∗
  (* the caller's own pid (read-only fraction) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through to sleep() *)
  procs_inv γs -∗
  (* THE CROSSING IS THE LITERAL [true], NOT [b].  acquiresleep PARKS (its
     wait loop sleeps), and a park moves the hart with interrupts off, so it
     has nothing to do with SIE -- the porting guide's "a PARKING function's
     [wp_next] index is [true] UNCONDITIONALLY".  While the contract was
     pinned at [b = true] the two spellings coincided and [b] was harmless;
     at [b = false] it would claim acquiresleep returns on the hart that
     called it, which is false. *)
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0 eb pj C b lks -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
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
   sleeps.  Design fs-icache.md 13.12 adopts Route B: the FREE branch takes
   the lock and returns, and the LOCKED branch NEVER REACHES A
   POSTCONDITION -- it is the wait loop, run at noff >= 2.

   WHAT THE LOCKED BRANCH ACTUALLY DOES is the one thing that changed when
   sleep was split in two, and it is worth being exact about, because the
   older reading ("it diverges in sched's panic") is no longer true.  Each
   iteration is sleep_prepare / release(&lk->lk) / sleep() /
   acquire(&lk->lk), and sleep() at noff >= 2 has TWO arms
   ([SpecSleep.wp_sleep_nested_body]): if [p->chan] is still armed it goes
   SLEEPING -> sched() -> panic("sched locks") and nothing comes back; if a
   wakeup cleared the channel inside the window it returns, noff-balanced,
   and the thread goes round the loop again.  Nothing can rule the second
   arm out (SpecSleep.v's header: [p_chan] is existential under p->lock and
   no receipt survives the window), so the branch is proved as a Löb loop
   rather than as a divergence -- the honest reading of a thread that keeps
   being woken and keeps finding the sleeplock taken.  Either way it has no
   exit, which is all this contract needs.

   So the nested contract is the ordinary one with

     - the level raised to [S n] and the resource index pinned to the
       LITERAL [false] ([cpu_own]'s enabled arm demands noff = 0, so a
       [b] binder would have exactly one live instance anyway);
     - NO [eb = true] parking premise.  It exists so a parking thread can
       hand the trap CSRs across a swtch; the returning branch never
       parks, and on the looping branch the swtch is on the arm that never
       comes back (the interior release pops to [S n], re-enabling
       nothing), so there is no crossing to pay for;
     - the crossing index [false] as well: the caller is inside its own
       critical section, so no leaf here can move the hart.

   The postcondition is otherwise IDENTICAL -- [sleeplocked], the pid
   cell, the protected [R] -- and the level comes back unchanged, i.e.
   the function is noff-balanced exactly as at level 0.

   REF-1 (design 5(b)) makes the LOCKED branch -- panic or wait loop --
   unreachable at iput's call site; we do not prove that, we permit it. *)
Definition wp_acquiresleep_nested_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac)
    (n : nat) (lks : gset nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  (* the interior acquire pushes to [S (S n)] and sleep's own acquire to
     [S (S (S n))], transiently +1 *)
  (Z.of_nat n + 4 < 2 ^ 31)%Z ->
  (* same order fact as the non-nested route, for the same "sleep lock"
     acquire; [lks] here is whatever the caller (e.g. iput, holding
     "itable") already has, and "sleep lock" (6) outranks "itable" (2), so
     [locks_below lks (lock_rank "itable")] (iput's own premise) is not
     enough by itself -- the caller must give the bound AT "sleep lock",
     i.e. [locks_below lks (lock_rank "sleep lock")], which subsumes it via
     [locks_below_mono]. *)
  locks_below lks (lock_rank "sleep lock") ->
  sie_cap_gpr m av false pj -∗
  (* NESTED: a spinlock IS held on entry, and is still held on exit *)
  cpu_own (S n) eb pj C false lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  panic_wp_any -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv γs -∗
  wp_next false pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av false pj -∗
      cpu_own (S n) eb pj C false lks -∗
      pc_is ret_tgt -∗
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ACQUIRESLEEP.
  Parameter wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}

      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac} (b : bool) (lks : gset nat),
      wp_acquiresleep_sconf_body γs j γl γsl s R m pidv av eb C dq b lks.
  Parameter wp_acquiresleep_nested_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac}
      (n : nat) (lks : gset nat),
      wp_acquiresleep_nested_body γs j γl γsl s R m pidv av eb C dq n lks.
End ACQUIRESLEEP.
