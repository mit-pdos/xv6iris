(* SpecAcquire.v -- the public interface of Acquire, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   The lock's [cpu] word is owned by the lock invariant (WpLock.v), so no cell
   is threaded here.  What the caller gets back is the [locked γl cpu_id]
   token, which PINS [lk->cpu] at this hart's [struct cpu] -- so release needs
   nothing else.

   A caller does NOT have to prove it is not already holding the lock: it
   supplies [panic_wp] (SpecPanic.v) instead, and acquire's
   [if(holding(lk)) panic] arm is discharged by that contract.  So the spec
   reads "acquire either returns holding the lock, or panics" -- exactly what
   the C code promises for a hart that violates the no-reentrance rule.

   ==================================================================== *)
(*  TWO TIERS OF HELD-SET PRECONDITION, AND WHY BOTH EXIST.

   Each contract below is an instance of ONE core body indexed by the
   precondition it puts on the caller's held set [lks]:

     FRESH   [s ∉ lks]            -- what the MACHINE needs.
     BELOW   [locks_below lks s]  -- what the DISCIPLINE requires.

   The proof consumes only the first.  All the ghost step does is insert [s]
   into this hart's held set, and a [gset] insert is sound exactly when the
   element is not already there (LockSet.v's header: an unconditional insert
   beside a membership tie is inconsistent).  Nothing in acquire's WP needs an
   ORDER at all -- the spin loop is a Löb loop, so a spec for a blocking
   acquire is provable however the locks are ranked.

   The order is therefore a POLICY, imposed here rather than discovered:
   [locks_below lks s] is the deadlock-freedom discipline (the held set is a
   chain in [LockRank.lock_rank]'s total order, so no cycle of waiting harts
   can form), and every ordinary caller must meet it.  Dropping to FRESH keeps
   the proof sound and gives up the global no-deadlock argument for that one
   call site, which then owes its own reason not to block.  Use it ONLY where
   such a reason exists and is written down; [iput]'s nested [acquiresleep] --
   licensed by icache REF-1 exclusivity rather than by rank -- is the case the
   tier exists for (claude-notes/completed/lock-set.md, "THE ONE UNLICENSED
   EDGE").

   BELOW IS A BOUND, NOT A NON-MEMBERSHIP, AND THE REASON IS COMPOSITION.  [∉]
   does not compose: a function that transitively acquires k locks needs k
   separate premises, and every caller inherits all of them, so the premise set
   grows with the transitive closure of the call graph.  [iput] alone would
   carry three ("itable" directly, "sleep lock" via acquiresleep, "log" via
   iupdate -> log_write).  The bound carries ONE, at the LOWEST rank the
   function touches, and the rest are consequences: [locks_below_mono] weakens
   it to every higher rank and [locks_below_not_elem] turns each into the
   non-membership the ghost step actually consumes.  Nesting composes too --
   [locks_below_union_singleton] takes [locks_below lks r] across an acquire at
   [r] to [locks_below ({[r]} ∪ lks) r'] for any [r < r'].  That is why BELOW,
   not FRESH, is what a FUNCTION contract states; FRESH is for the one call
   site that cannot state a bound.

   NEITHER TIER KILLS THE [if(holding(lk)) panic] ARM, and [panic_wp_any]
   therefore stays in both.  The refutation needs the held-set FRAGMENT
   ([WpLock.lk_cpu_frag]) in scope where [holding]'s read decides [phi], and
   [WpSconfLock.wp_ld_lkcpu_lockopen_gen]'s view premise is handed only
   [lock_auth γl st] and the caller's token -- not the fragment, which is not
   persistent and would have to be borrowed and returned inside the invariant
   open.  That leaf change plus a [SpecHolding] variant concluding [a0 = 0] is
   a separate piece of work. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
From Stdlib Require Import FunctionalExtensionality.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import PanicStub.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


(* The generic form, over [lock_openable] (WpLock.v): the right to TOUCH the
   lock is the resource [Tc], presented on the way in and handed back on the
   way out -- for a kalloc'd object that is a REFERENCE to it, which is what
   makes the storage reclaimable (a hart with no reference cannot even take
   the lock).  acquire opens the invariant four times; the first three present
   [Tc] and the last presents the [locked_pre] token it has just won, so the
   caller owes a refutation of the dead state [Dc] for each.  acquire disposes
   of nothing, so [Dc] merely rides along.  A static kernel lock instantiates
   at [Dc := False] ([wp_acquire_pre_body] below).

   [pre] is the held-set precondition; see the tier note in the file header.
   It is the LAST argument so that it reads as an index on an otherwise fixed
   contract, exactly as [lks] itself does on [cpu_own]. *)
Definition wp_acquire_gen_pre_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) (pre : Prop) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  pre ->
  (⊢ Tc -∗ Dc -∗ False) ->
  (* [∀ i : CPU], not pinned at the entry [cpu_id]: acquire's entry can be at
     [b = true] (the enabled arm forces [n = 0]), so "enter at CID with
     interrupts on, migrate during the 7-instruction prologue, win the lock
     as CIDpo" is a REAL execution -- the caller's entry-hart credential is
     the wrong credential, since the leaf [wp_csd_lkcpu_lockopen_s_sconf]
     fixes the hart at its OWN (the post-migration) ambient identity.
     Strengthening this premise to every hart costs [AcquireOfGen] nothing:
     [lock_refute_False] is already hart-generic. *)
  (forall i : CPU, ⊢ locked_pre γl i -∗ Dc -∗ False) ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lk0 s R Dc -∗
  Tc -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    Tc -∗
    (* [false], NOT [b]: acquire is UNBALANCED -- it opens with push_off(),
       which disables interrupts regardless of the entry state, and returns
       still holding the lock.  The [wp_next] index stays [b] (a trap CAN land
       on acquire's first instruction, before it disables), which is exactly
       the resource-index / wp_next-index divergence documented in the porting
       guide.  Threading [b] out made release -- whose entry is [false] --
       uncallable.

       AND [trap_res b + av], NOT [av]: acquire's push_off is the point at
       which the ARM-DEPENDENT trap reserve of [IntrDefs.sie_cap] moves into
       the usable count.  The total carve is conserved -- entry carve
       [trap_res b + av], exit carve [trap_res false + (trap_res b + av)] =
       [trap_res b + av] -- so this is a pure re-indexing of the SAME stack
       ownership, not a split: the [kv_frame_slots] an enabled caller was
       holding against a trap become ordinary usable stack for the
       interrupts-off critical section, where nothing can trap.  At
       [b = false] the index is [trap_res false + av], DEFINITIONALLY [av],
       so an interrupts-off caller reads verbatim as before.  The matching
       [Release] entry index is [trap_res outb + av] with [outb] forced equal
       to [b] by [cpu_own], so the acquire/release pair composes back to [av]
       syntactically and no [kv_frame_slots <= _] premise appears anywhere.
       [10 <= av] does not move: [av] is still the ENTRY usable count. *)
    sie_cap_gpr mfin (trap_res b + av)%nat false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mfin ⌝ -∗
    locked γl cpu_id -∗ R -∗
    cpu_own (S n) eb p false ({[s]} ∪ lks) -∗
    arm_pay n eb p -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* THE FRESH TIER: the premise the ghost step actually consumes.  This is the
   lowest-level contract acquire has, and the only one its proof discharges
   directly. *)
Definition wp_acquire_gen_fresh_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  wp_acquire_gen_pre_body γl s R Tc Dc m n eb p av b lks (s ∉ lks).

(* THE BELOW TIER: the deadlock-freedom discipline, and what every ordinary
   caller states. *)
Definition wp_acquire_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  wp_acquire_gen_pre_body γl s R Tc Dc m n eb p av b lks (locks_below lks s).

(* the contract is ANTITONE in its precondition -- which is the whole content
   of the tiering, and is what makes BELOW a corollary of FRESH rather than a
   second proof. *)
Lemma wp_acquire_gen_pre_weaken `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool)
    (p : mword 64) (av : nat) (b : bool) (lks : gset string) (pre pre' : Prop) :
  (pre' -> pre) ->
  wp_acquire_gen_pre_body γl s R Tc Dc m n eb p av b lks pre ->
  wp_acquire_gen_pre_body γl s R Tc Dc m n eb p av b lks pre'.
Proof.
  cbv beta zeta delta [wp_acquire_gen_pre_body].
  intros Himp H Hpos Hav Hpre' Href Hrefpre.
  exact (H Hpos Hav (Himp Hpre') Href Hrefpre).
Qed.

(* ---- the static-kernel-lock level: same two tiers over [is_lock] -------- *)

Definition wp_acquire_pre_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) (pre : Prop) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquire in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  pre ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lk0 s R -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    (* see [wp_acquire_gen_pre_body] for why the exit is at [false] and at
       [trap_res b + av] rather than at [b] and [av]. *)
    sie_cap_gpr mfin (trap_res b + av)%nat false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mfin ⌝ -∗
    locked γl cpu_id -∗ R -∗
    cpu_own (S n) eb p false ({[s]} ∪ lks) -∗
    arm_pay n eb p -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Definition wp_acquire_fresh_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  wp_acquire_pre_body γl s R m n eb p av b lks (s ∉ lks).

Definition wp_acquire_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  wp_acquire_pre_body γl s R m n eb p av b lks (locks_below lks s).

Lemma wp_acquire_pre_weaken `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
    (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool)
    (p : mword 64) (av : nat) (b : bool) (lks : gset string) (pre pre' : Prop) :
  (pre' -> pre) ->
  wp_acquire_pre_body γl s R m n eb p av b lks pre ->
  wp_acquire_pre_body γl s R m n eb p av b lks pre'.
Proof.
  cbv beta zeta delta [wp_acquire_pre_body].
  intros Himp H Hpos Hav Hpre'.
  exact (H Hpos Hav (Himp Hpre')).
Qed.

Module Type ACQUIRE_GEN.
  Parameter wp_acquire_gen_fresh_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_acquire_gen_fresh_sconf_body γl s R Tc Dc m n eb p av b lks.
  Parameter wp_acquire_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R Tc Dc : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_acquire_gen_sconf_body γl s R Tc Dc m n eb p av b lks.
End ACQUIRE_GEN.

Module Type ACQUIRE.
  Parameter wp_acquire_fresh_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_acquire_fresh_sconf_body γl s R m n eb p av b lks.
  Parameter wp_acquire_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_acquire_sconf_body γl s R m n eb p av b lks.
End ACQUIRE.
