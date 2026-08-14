(* SpecSleep.v -- the public interface of sleep(), stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void sleep(void) {
       struct proc *p = myproc();
       acquire(&p->lock);
       if (p->chan != 0) { p->state = SLEEPING; sched(); }
       release(&p->lock);
     }

   THE CONDITION LOCK IS GONE FROM THIS CONTRACT, and that is the whole
   change.  xv6 used to spell the sleep protocol as one function

       sleep(chan, lk)   /* takes p->lock, releases lk, parks, re-acquires lk */

   whose contract therefore had to name the caller's lock (γk / lka / Rk),
   its resource, and -- once a pipe's cancellable lock wanted the same
   treatment -- a credential [Tk], a dead state [Dk] and three refutations,
   in a whole second [SLEEP_GEN] interface.  The protocol is now split in
   two, and the caller does the lock work itself:

       sleep_prepare(chan);   /* SpecSleepPrepare.v: record the channel   */
       release(lk);           /* the caller's own release                 */
       sleep();               /* park, if no wakeup arrived meanwhile     */
       acquire(lk);           /* the caller's own re-acquire              */

   so everything lock-shaped moved to where it belongs -- the ordinary
   acquire/release contracts, which are already [lock_openable]-generic
   (ACQUIRE_GEN / RELEASE_GEN).  [SLEEP_GEN] is deleted, not ported.

   WHAT IS LEFT IS YIELD'S CONTRACT (SpecYield.v), verbatim but for the
   entry pc: a thread at noff = 0 acquires its own p->lock, parks through
   sched(), and -- once some scheduler dispatches it again -- releases and
   returns.  Read SpecYield.v's header for the reasoning behind each line;
   the two differ only in

     - the state stored before the park (SLEEPING here, RUNNABLE there),
       which no caller can observe, both being [park_ok]; and
     - THE PARK IS CONDITIONAL.  sleep() reads [p->chan] under p->lock and
       parks only if it is non-zero -- wakeup() clears the field, so a
       wakeup that landed between the caller's sleep_prepare and here makes
       sleep a no-op instead of a lost wakeup.  The contract does not case
       on this: [wp_next true pj] already quantifies the continuation over
       the resuming hart, and the no-park arm simply instantiates it at the
       hart it is already on.  (Nothing here promises the wakeup HAPPENS --
       that is liveness; this promises what holds when sleep returns.)

   [eb] IS NOT PINNED, for yield's reason: the trap cone reaches sleep with
   interrupts off, so the acquire inside records intena = 0 and the whole
   call runs at [eb = false].  Hence the trap CSRs and the running claim are
   premises, in their [_ext] form: at [eb = true] sleep's own acquire
   produces them out of the enabled SIE arm and [trap_csrs_ext true = emp];
   at [eb = false] there is no arm to dismantle and the caller brings them.
   sched's crossing demands the set unconditionally, and sepc/scause/stval
   are PER-HART, so a parking function cannot frame them.

   THE CROSSING INDEX IS THE LITERAL [true]: a swtch moves the hart with
   interrupts off, so a park is a hart change that has nothing to do with
   SIE.  Threading [eb] there would claim, at [eb = false], that sleep
   returns on the hart that called it.

   The second interface below, [wp_sleep_nested_body], is what a caller that
   is ALREADY holding a spinlock gets.  It used to be a pure divergence
   claim; the conditional park makes that false, and its header explains
   why. *)
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
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (20 <= av)%nat ->
  (* THE ORDER PREMISE FOR SLEEP'S OWN ACQUIRE.  The split protocol left
     sleep holding NO caller lock on entry, but sleep still takes p->lock
     itself (proc.c: [acquire(&p->lock)] before the state store), so acquire's
     [locks_below lks s] has to come from here.  BALANCED in
     the held set -- the release at +0x22 gives the rank straight back on both
     arms -- so [lks] is unchanged in the postcondition, and this premise is
     exactly what makes the insert/delete cancel ([locks_below_not_elem]).
     Trivial at [lks = ∅] ([locks_below_empty]), which is every real call site
     (sleep is only ever reached from a thread that has already released its
     condition lock). *)
  locks_below lks "proc"%string ->
  sie_cap_gpr m av eb pj -∗
  cpu_own 0 eb pj C eb lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  trap_csrs_ext eb -∗
  cpu_claim_ext eb pj -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr mf av eb pj -∗
      cpu_own 0 eb pj C eb lks -∗
      pc_is ret_tgt -∗
      trap_csrs_ext eb -∗
      cpu_claim_ext eb pj -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  ROUTE B, LEMMA (2): sleep ENTERED WITH A SPINLOCK HELD.               *)
(* ===================================================================== *)
(* sleep() takes p->lock, so a thread that enters it already holding a
   spinlock reaches sched() at noff >= 2 -- and sched panics ("sched locks",
   [SpecSched.wp_sched_locks_body]).  This is design fs-icache.md 13.12's
   middle lemma: it is what makes the LOCKED branch of a nested
   [acquiresleep] safe.

   IT IS NO LONGER A DIVERGENCE LEMMA, and that is the split protocol's one
   real cost.  The old sleep(chan, lk) parked UNCONDITIONALLY, so entering it
   with a lock held reached the panic and nothing came back; the new sleep
   parks only if [p->chan] is still non-zero, and the [beqz] at +0x16 takes
   the thread straight to the release and the [c.ret].  So there are two
   arms, and only one of them panics:

     - chan <> 0 (nobody woke us between the caller's sleep_prepare and
       here): SLEEPING, sched(), panic.  Diverges, as before.
     - chan = 0 (a wakeup landed in the window): no park, release p->lock,
       RETURN -- noff-balanced, back at [S n].

   AND NOTHING CAN RULE THE SECOND ARM OUT.  [p_chan] sits under an
   EXISTENTIAL in [SchedCtx.proc_lock_res] and [SpecSleepPrepare]'s
   postcondition is deliberately empty, so a caller holds no receipt saying
   the channel is still armed -- nor could one exist, because wakeup()
   clears the field holding only p->lock, so no fraction of "chan <> 0"
   survives the window.  Claiming divergence here would be claiming
   something false about a real trace.

   Hence the continuation.  Note what it does NOT need: no [wp_next], and no
   trap CSRs.  At [n >= 1] the interior release pops to [S n] rather than 0,
   so it re-enables nothing and the hart cannot move; and the swtch that
   would have demanded the CSRs is on the arm that never returns.

   The old spelling of this lemma also took the caller's condition lock,
   because sleep(chan, lk) released it on the way to sched().  The split
   protocol releases nothing, so this lemma consumes NOTHING -- which is why
   the [lock_openable]-generic twin it used to need ([wp_sleep_gen_locks])
   has no reason to exist any more.

   For the nested [acquiresleep] this is still enough, and the shape of the
   argument is the only thing that changes: its LOCKED branch used to end in
   a divergence and now ends in a Löb loop (sleep_prepare / release / sleep /
   acquire, forever), which is the honest reading of a thread that keeps
   being woken and keeps finding the sleeplock taken.  REF-1
   (design/fs-icache.md 5(b)) makes both unreachable at iput's call site; we
   do not prove that, we permit it. *)
Definition wp_sleep_nested_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (n : nat) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sleep in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (20 <= av)%nat ->
  (* the interior acquire reaches [S (S n)], transiently +1 *)
  (Z.of_nat n + 3 < 2 ^ 31)%Z ->
  (* AND IT IS STILL SLEEP'S OWN ACQUIRE THAT NEEDS THIS, not the caller's
     lock: [lks] here is the set the caller already holds (it is at [S n], so
     [lks] is non-empty), and every rank in it must sit strictly BELOW
     p->lock's -- which is the real xv6 order (a nested sleeper holds
     "sleep lock" at 6 or "log" at 3, both under "proc" at 11).  Both arms
     stay balanced in the set -- the no-park arm releases what it took, the
     park arm panics inside sched and never returns -- so the postcondition
     carries the entry [lks] unchanged. *)
  locks_below lks "proc"%string ->
  sie_cap_gpr m av false pj -∗
  cpu_own (S n) eb pj C false lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  (∀ (mf : regfile),
     ⌜callee_saved m mf⌝ -∗
     sie_cap_gpr mf av false pj -∗
     cpu_own (S n) eb pj C false lks -∗
     pc_is ret_tgt -∗
     WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SLEEP.
  Parameter wp_sleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (lks : gset string),
      wp_sleep_sconf_body γs j γl m av eb C lks.
  Parameter wp_sleep_nested :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (C : iProp Σ) (n : nat) (lks : gset string),
      wp_sleep_nested_body γs j γl m av eb C n lks.
End SLEEP.
