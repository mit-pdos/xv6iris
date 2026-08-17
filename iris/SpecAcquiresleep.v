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
   0): sleep() requires exactly one level outstanding, which forces it.

   FIVE CONTRACTS, IN THREE PAIRS OF ONE IDEA.  Each of the two blocking
   levels -- level 0 and the NESTED one iput needs -- is stated once over the
   sleeplock's holder DEPOSIT [H : Qp -> iProp Σ] (SleepLock.v) and once at
   the untracked instance [H := sl_untracked], [q := 1], which is what every
   existing caller takes and which reads exactly as it did before the deposit
   existed.  The fifth, [wp_acquiresleep_nb_body], is the NON-BLOCKING nested
   contract: same postcondition, but its precondition is evidence that the
   lock is FREE rather than a lock-order bound, so its wait loop is refuted
   rather than proved.  See the block above it. *)
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
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Import Defs.


(* ==================================================================== *)
(*  THE HOLDER DEPOSIT [H] (SleepLock.v), AND WHY IT IS ON THE CONTRACT.

   Taking a sleeplock leaves a resource of the acquirer's OWN inside it --
   [H q], where [q] is the fraction of the "may hold this lock" right the
   caller is spending.  Nothing else can be refutable from outside: what a
   would-be prover of "this lock is FREE" holds is a frame for the acquire's
   ghost step, so a held arm manufactured out of the free arm alone survives
   that frame (SleepLock.v's header).  releasesleep hands the same fraction
   back, pinned by the holder's token [sleeplocked_q γsl q].

   [wp_acquiresleep_sconf_body] below is this at the UNTRACKED instance
   ([H := sl_untracked], [q := 1]), where the deposit is [emp] and the
   fraction is invisible -- which is exactly what every existing caller
   (bget, ilock) takes, unchanged.  The tracked instance ([H := slh_tok γsl])
   is what makes [wp_acquiresleep_nb_body] at the foot of this file possible. *)
Definition wp_acquiresleep_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (dq : dfrac) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  locks_below lks "sleep lock" ->
  sie_cap_gpr kt m av b pj -∗
  cpu_own 0 eb pj b lks -∗
  trap_csrs_ext kt eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock_gen γl γsl slk s R H -∗
  (* THE DEPOSIT, spent into the lock and recovered by releasesleep *)
  H q -∗
  p_pid pj ↦₄{dq} pidv -∗
  procs_inv (kt := kt) γs -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr kt mf av b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext kt eb -∗
      cpu_claim_ext eb pj -∗
      pc_is ret_tgt -∗
      sleeplocked_q γsl q -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_acquiresleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    
    (kt : ktier) (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (dq : dfrac) (b : bool) (lks : gset string) :=
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
  locks_below lks "sleep lock" ->
  sie_cap_gpr kt m av b pj -∗
  cpu_own 0 eb pj b lks -∗
  (* WHAT THE PARK NEEDS, AND WHERE IT COMES FROM.  Everything below sleeps,
     and a parking thread must hand [trap_csrs] and [cpu_claim] across the
     crossing (SpecSched.v).  At [eb = true] acquiresleep's OWN acquire frees
     them out of [sie_arm true], so the complement is [emp] and the caller
     brings nothing -- which is why this used to be an [eb = true] premise
     instead.  At [eb = false] the push_off frees nothing and the caller
     brings the pair, holding it because the TRAP handed it over; that is the
     case iput/ilock need, and through them kexit and usertrap. *)
  trap_csrs_ext kt eb -∗
  cpu_claim_ext eb pj -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the caller's own pid (read-only fraction) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through to sleep() *)
  procs_inv (kt := kt) γs -∗
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
      sie_cap_gpr kt mf av b pj -∗
      cpu_own 0 eb pj b lks -∗
      trap_csrs_ext kt eb -∗
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
(*  THE NESTED BLOCKING CONTRACT IS GONE, AND THAT IS THE POINT.          *)
(* ===================================================================== *)
(* iput calls acquiresleep(&ip->lock) while HOLDING itable.lock -- the
   kernel's only nested acquiresleep (fs.c:348) -- so this file used to
   publish a contract entered at noff >= 2, whose LOCKED branch was the wait
   loop: sleep_prepare / release / sleep / acquire, forever, with
   [sleep] at noff >= 2 reaching sched() and panic("sched locks").  It was
   provable ONLY because [SpecSleep] offered that panic as an arm.

   Its sole consumer was iput, and iput now takes the NON-BLOCKING contract
   below.  So every acquiresleep that can SLEEP is entered at noff = 0
   ([wp_acquiresleep_gen_sconf]'s [cpu_own 0]), sleep's own acquire puts it
   at exactly noff = 1 for the call to sched, and sched's "sched locks"
   panic became unreachable rather than permitted -- SpecSched.v now has no
   noff <> 1 contract at all.
   (claude-notes/projects/iput-acquiresleep.md.) *)

(* ===================================================================== *)
(*  THE NON-BLOCKING NESTED CONTRACT.                                     *)
(* ===================================================================== *)
(* A BLOCKING acquiresleep's wait loop reaches [sleep_prepare], which acquires
   [p->lock] at "proc" (9).  A caller that already holds a lock ABOVE
   "sleep lock" -- [iput] holds "itable" (14) -- can hand it no such bound,
   and none is true.  That was the whole content of the FALSE axiom
   [ProofIput.iput_acquiresleep_order_ADMITTED], now discharged
   (claude-notes/projects/iput-acquiresleep.md).

   THE DISCHARGE CHANGES THE OBLIGATION.  Here the caller instead presents
   [slh_auth γt None], the AUTHORITATIVE ZERO of the object's
   outstanding-share count: no share of the "may hold this lock" right exists
   anywhere, so no deposit sits in the lock, so the [lk->locked != 0] arm of
   [sl_res_gen] is REFUTED at the leaf that reads the word.  The loop is not
   proved, it is unreachable -- so [sleep_prepare] is never reached, so no
   order premise is raised, and all that is left of the held-set precondition
   is what the interior [acquire(&slk->lk)]'s ghost step consumes:
   [SpecAcquire]'s FRESH tier, ["sleep lock" ∉ lks].

   WHAT COMES BACK.  The deposit this call makes is minted from the zero on
   the way in, so the caller leaves with [slh_auth γsl (Some q)] beside its
   holder token; [SleepLock.slh_return_last] turns that back into the zero
   once releasesleep returns the share.

   The sleep cone is gone from the contract with the loop: no [procs_inv], no
   [γs], no [j < NPROC].  What is left is the prologue, the entry acquire, the
   [locked := 1] / [pid := myproc()->pid] stores and the interior release.

   THIS IS THE ONLY WAY TO TAKE A SLEEPLOCK WITH A SPINLOCK HELD.  The
   blocking contracts are all at [cpu_own 0], which is what makes sched's
   [noff != 1] panic unreachable from here. *)
Definition wp_acquiresleep_nb_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (* THE DEPOSIT'S OWN GNAME, separate from the lock's.  A client keys the
       "may hold" right by the OBJECT rather than by the lock -- the icache
       keys it by the inode SLOT ([IcacheRef.icfg_isl k]) so that a reference
       can carry it -- and the refutation only ever looks at this one. *)
    (γt : gname) (q : Qp)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (dq : dfrac)
    (n : nat) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (26 <= av)%nat ->
  (Z.of_nat n + 4 < 2 ^ 31)%Z ->
  (* NOT a rank bound: only what the held-set insert needs. *)
  "sleep lock" ∉ lks ->
  sie_cap_gpr kt m av false pj -∗
  cpu_own (S n) eb pj false lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock_gen γl γsl slk s R (slh_tok γt) -∗
  (* THE EVIDENCE THAT THE LOCK IS FREE *)
  slh_auth γt None -∗
  p_pid pj ↦₄{dq} pidv -∗
  wp_next false pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr kt mf av false pj -∗
      cpu_own (S n) eb pj false lks -∗
      pc_is ret_tgt -∗
      sleeplocked_q γsl q -∗
      slh_auth γt (Some q) -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type ACQUIRESLEEP.
  Parameter wp_acquiresleep_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ) (H : Qp -> iProp Σ) (q : Qp)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) {dq : dfrac} (b : bool) (lks : gset string),
      wp_acquiresleep_gen_sconf_body kt γs j γl γsl s R H q m pidv av eb dq b lks.
  Parameter wp_acquiresleep_nb_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ) (γt : gname) (q : Qp)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) {dq : dfrac}
      (n : nat) (lks : gset string),
      wp_acquiresleep_nb_body kt j γl γsl s R γt q m pidv av eb dq n lks.
  Parameter wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}

      (kt : ktier) (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) {dq : dfrac} (b : bool) (lks : gset string),
      wp_acquiresleep_sconf_body kt γs j γl γsl s R m pidv av eb dq b lks.
End ACQUIRESLEEP.
