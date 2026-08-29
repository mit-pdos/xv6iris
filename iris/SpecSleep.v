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

   THERE IS NO SECOND INTERFACE.  A caller already holding a spinlock used
   to get [wp_sleep_nested_body], whose park arm walked into sched's
   "sched locks" panic; nothing calls it now, and the comment block below
   the contract says what took its place. *)
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
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Import Defs.


Definition wp_sleep_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (γs : list gname) (j : nat) (γl : gname)
    (m : regfile) (av : nat) (eb : bool) (lks : gset string) :=
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
  sie_cap_gpr KT1 m av eb pj -∗
  cpu_own 0 eb pj eb lks -∗
  kernel_text -∗ pc_is pcE -∗
  procs_inv γs -∗
  trap_csrs_ext KT1 eb -∗
  cpu_claim_ext eb pj -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜callee_saved m mf⌝ -∗
      sie_cap_gpr KT1 mf av eb pj -∗
      cpu_own 0 eb pj eb lks -∗
      pc_is ret_tgt -∗
      trap_csrs_ext KT1 eb -∗
      cpu_claim_ext eb pj -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* ===================================================================== *)
(*  SLEEP HAS NO WITH-A-SPINLOCK-HELD CONTRACT ANY MORE.                  *)
(* ===================================================================== *)
(* [wp_sleep_nested] entered at noff = [S n], reached sched() at [S (S n)]
   on its park arm, and let sched panic ("sched locks") there.  Its one
   client was the LOCKED branch of a nested [acquiresleep]; iput now takes
   [SpecAcquiresleep.wp_acquiresleep_nb_sconf] instead, which proves it never
   sleeps, so the lemma is deleted together with the
   [SpecSched.wp_sched_locks] it stood on
   (claude-notes/projects/iput-acquiresleep.md).

   [wp_sleep_sconf] above therefore demands [cpu_own 0] unconditionally, and
   it is the only way in.  Sleep's own [acquire(&p->lock)] then puts the
   thread at exactly noff = 1 for the call to sched -- which is what sched's
   check wants, and why that panic is now unreachable rather than permitted. *)

Module Type SLEEP.
  Parameter wp_sleep_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (γs : list gname) (j : nat) (γl : gname)
      (m : regfile) (av : nat) (eb : bool) (lks : gset string),
      wp_sleep_sconf_body γs j γl m av eb lks.
End SLEEP.
