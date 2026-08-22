(* LockSet.v -- THE PER-CPU HELD-LOCK SET, ORDERED.

   Every hart owns a ghost set of the NAMES (the string [initlock] was given)
   of the spinlocks it currently holds; the ORDER on those names is
   [LockRank.lock_rank], and it lives in [locks_below] rather than in the set.
   The
   authority rides in [IntrDefs.cpu_hart] -- with the running kernel thread
   while interrupts are off, inside [sie_arm true] while they are on -- and a
   lock whose [lk->cpu] field is SET keeps the matching fragment
   [lk_in i s] inside its own invariant ([WpLock.lock_inv]).  So

       "lk->cpu = &cpus[i]"   and   "name(lk) is in hart i's held set"

   are ONE fact, not two: the fragment cannot be forged and cannot be
   duplicated, and agreement against the authority reads the membership off it
   ([cpu_locks_in]).

   ---------------------------------------------------------------------
   WHY RANKS, AND WHAT THAT DELETED

   [gset_disj] gives exclusivity and unforgeability, but minting a fragment
   needs [r ∉ S].  That is supplied by acquire's ORDER PREMISE
   ([LockRank.locks_below S r], via [locks_below_not_elem]) -- "everything you
   hold ranks strictly below the lock you are taking", which is the deadlock
   discipline itself and is trivial at [S = ∅].

   This is the whole reason the set is cheap.  The predecessor keyed on lock
   ADDRESSES and had no order premise, so it had to DERIVE [lk ∉ S] from the
   machine: the hart co-owned HALF of every held lock's [lk->cpu] cell, pinned
   at [cpus_ptr i], and freshness fell out of the cell disagreeing at 0.  With
   the premise supplying freshness directly, that half-cell apparatus
   ([lk_stake], [lk_cpu_half], the 1/2 fractions and the two exchange wands in
   the cpu-word store leaves) is gone: the lock invariant owns its [lk->cpu]
   cell WHOLE in every state, and the set is pure ghost -- [cpu_locks_at] is
   the authority and nothing else, with no big-op over held locks.

   Two consequences worth knowing:

   - the fragment's exclusivity now says NO TWO LOCKS OF THE SAME FAMILY may
     be held at once, which is a restriction xv6 satisfies (LockRank.v's
     header) and which acquire's premise already implies;
   - [set_solver] WORKS here.  Over [gset (mword n)] it crashes with "No
     matching clauses for match" -- Sail's [Decidable_eq_mword] against
     stdpp's [bv_eq_dec] -- which is why the durable notes carry a
     discharge-by-named-lemma rule for this file.  With [nat] elements that
     rule no longer applies and the named-lemma spellings below are ordinary
     stdpp.

   ---------------------------------------------------------------------
   THE TIE IS STILL A FACT ABOUT THE MACHINE, and it is what makes acquire's
   [if(holding(lk)) panic] arm DEAD rather than merely discharged: a hart
   whose set omits [rank lk] cannot have [lk->cpu = cpus_ptr i], because the
   only state in which the cell reads [cpus_ptr i] is the one whose invariant
   holds [lk_in i (rank lk)] -- and that agrees against the authority.  See
   [WpLock.lock_inv] for where the fragment sits. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Export LockRank.
Local Open Scope Z_scope.

Section LockSet.
  Context `{!riscvGS Σ}.

  (* [lk->cpu]: the 8-byte owner field at +16, in the address form the
     acquire / release / holding leaves see it ([add_vec lk (sext 16)]).
     It lives HERE rather than in WpLock.v because the held-lock set is
     stated over it; WpLock.v re-exports this file. *)
  Definition lock_cpu (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)).

  (* ---- the ghost pieces --------------------------------------------- *)

  (* the authority: hart [i]'s held set, as RANKS.  Canonically named, so no
     contract carries a [γ] (RiscvPtsto.era_lockset_name). *)
  Definition lk_auth (i : CPU) (S : gset string) : iProp Σ :=
    own (lockset_name i) (● (GSet S) : lockSetR).

  (* THE MEMBERSHIP FACT a lock with [lk->cpu] set keeps in its invariant. *)
  Definition lk_in (i : CPU) (r : string) : iProp Σ :=
    own (lockset_name i) (◯ (GSet {[r]}) : lockSetR).

  (* THE SET, as hart [i] owns it.  Pure ghost: the half-cell stakes the
     address-keyed predecessor carried alongside are gone (see the header). *)
  Definition cpu_locks_at (i : CPU) (S : gset string) : iProp Σ :=
    lk_auth i S.

  Global Instance lk_auth_timeless i S : Timeless (lk_auth i S).
  Proof. apply _. Qed.
  Global Instance lk_in_timeless i r : Timeless (lk_in i r).
  Proof. apply _. Qed.
  Global Instance cpu_locks_at_timeless i S : Timeless (cpu_locks_at i S).
  Proof. apply _. Qed.

  (* ---- the laws ------------------------------------------------------ *)

  (* THE TIE: the fragment a held lock keeps pins its rank into the set. *)
  Lemma lk_in_agree (i : CPU) (S : gset string) (r : string) :
    lk_auth i S -∗ lk_in i r -∗ ⌜r ∈ S⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply gset_disj_included in Hincl.
    apply singleton_subseteq_l in Hincl. exact Hincl.
  Qed.

  Lemma cpu_locks_in (i : CPU) (S : gset string) (r : string) :
    cpu_locks_at i S -∗ lk_in i r -∗ ⌜r ∈ S⌝.
  Proof. iIntros "Ha Hf". iApply (lk_in_agree with "Ha Hf"). Qed.

  (* THE FORM ACQUIRE USES, contrapositively: a rank this hart does not hold
     cannot belong to a lock whose invariant is in the [Some (i, true)] state,
     because that state keeps [lk_in i r].  This is what makes the
     [if(holding(lk)) panic] arm dead.

     Stated at NON-MEMBERSHIP, which is all the refutation needs.  The lock
     ORDER gives it via [locks_below_not_elem] ([cpu_locks_not_in_below]
     below) once deadlock-freedom lands. *)
  Lemma cpu_locks_not_in (i : CPU) (S : gset string) (r : string) :
    r ∉ S ->
    cpu_locks_at i S -∗ lk_in i r -∗ False.
  Proof.
    iIntros (Hnin) "Ha Hf".
    iDestruct (cpu_locks_in with "Ha Hf") as %Hin.
    iPureIntro. exact (Hnin Hin).
  Qed.

  Lemma cpu_locks_not_in_below (i : CPU) (S : gset string) (r : string) :
    locks_below S r ->
    cpu_locks_at i S -∗ lk_in i r -∗ False.
  Proof. intros Hb. apply cpu_locks_not_in, locks_below_not_elem, Hb. Qed.

  (* the fragment is EXCLUSIVE -- one hart cannot hold two locks of the same
     rank, i.e. two of the same FAMILY.  xv6 never does (LockRank.v), and
     acquire's order premise forbids it independently. *)
  Lemma lk_in_excl (i : CPU) (r : string) :
    lk_in i r -∗ lk_in i r -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hv.
    iPureIntro. set_solver.
  Qed.

  (* acquire's ghost step.  The side condition is the order premise, not a
     fact read off the machine -- which is the whole simplification. *)
  Lemma cpu_locks_insert (i : CPU) (S : gset string) (r : string) :
    r ∉ S ->
    cpu_locks_at i S ==∗ cpu_locks_at i ({[r]} ∪ S) ∗ lk_in i r.
  Proof.
    iIntros (Hnin) "Ha".
    assert (Hdisj : {[r]} ## S) by set_solver.
    iMod (own_update _ _ ((● (GSet ({[r]} ∪ S)) ⋅ ◯ (GSet {[r]})) : lockSetR)
            with "Ha") as "[Ha Hf]".
    { apply auth_update_alloc.
      apply gset_disj_alloc_empty_local_update. exact Hdisj. }
    iModIntro. iFrame "Hf Ha".
  Qed.

  (* the spelling acquire actually meets: the premise it already carries. *)
  Lemma cpu_locks_insert_below (i : CPU) (S : gset string) (r : string) :
    locks_below S r ->
    cpu_locks_at i S ==∗ cpu_locks_at i ({[r]} ∪ S) ∗ lk_in i r.
  Proof.
    intros Hb. apply cpu_locks_insert, locks_below_not_elem, Hb.
  Qed.

  (* release's ghost step: the fragment is the licence to retire the rank. *)
  Lemma cpu_locks_delete (i : CPU) (S : gset string) (r : string) :
    cpu_locks_at i S -∗ lk_in i r ==∗
    ⌜r ∈ S⌝ ∗ cpu_locks_at i (S ∖ {[r]}).
  Proof.
    iIntros "Ha Hf".
    iDestruct (cpu_locks_in with "Ha Hf") as %Hin.
    iMod (own_update_2 _ _ _ ((● (GSet (S ∖ {[r]}))) : lockSetR) with "Ha Hf")
      as "Ha".
    { apply auth_update_dealloc. apply gset_disj_dealloc_local_update. }
    iModIntro. iFrame "Ha". iPureIntro. exact Hin.
  Qed.

  (* boot: the authority arrives from adequacy at the empty set. *)
  Lemma cpu_locks_intro_empty (i : CPU) :
    lk_auth i ∅ -∗ cpu_locks_at i ∅.
  Proof. iIntros "Ha". iFrame "Ha". Qed.

  (* ---- THE LEVEL/SET COUPLING -------------------------------------------

     [size lks <= n]: the hart holds no more locks than it has outstanding
     [push_off]s.  It is TRUE because every acquire pushes exactly once and
     every release pops exactly once, while a BARE push_off/pop_off pair moves
     [n] without touching the set.

     WHAT IT BUYS, and it is the reason it exists: at [n = 0] it reads
     [size lks <= 0], i.e. [lks = ∅].  That is exactly what pop_off's
     re-enabling branch must produce -- [cpu_own]'s [b = true] arm demands an
     empty held set -- so "you may only turn interrupts back on holding no
     spinlock" becomes DERIVED from the counting discipline rather than
     imposed as a separate conjunct.

     WHY IT IS BUNDLED WITH THE AUTHORITY rather than added as a third
     conjunct of [cpu_priv]: 24 sites across 8 files destructure the cpu
     bundle positionally, and keeping [cpu_priv] at two conjuncts leaves every
     one of those patterns matching unchanged.

     IT IS NOT PRESERVED BY A BARE [pop_off] ON ITS OWN -- unwinding [S n] to
     [n] with the set untouched needs [size lks <= n], which the invariant at
     [S n] does not give.  pop_off therefore takes it as a PREMISE, and that
     premise is the honest content of "you may only unwind a push once
     whatever it was paired with is gone": release discharges it because it
     has just deleted a rank ([size (lks ∖ {[r]}) = size lks - 1 <= n]), and a
     bare pusher discharges it from its own pre-push fact, which is pure and
     therefore still in context at the pop. *)
  Definition cpu_locks_lvl_at (i : CPU) (n : nat) (lks : gset string) : iProp Σ :=
    (cpu_locks_at i lks ∗ ⌜(size lks <= n)%nat⌝)%I.

  Lemma cpu_locks_lvl_at_elim (i : CPU) (n : nat) (lks : gset string) :
    cpu_locks_lvl_at i n lks -∗ cpu_locks_at i lks ∗ ⌜(size lks <= n)%nat⌝.
  Proof. iIntros "[$ $]". Qed.

  Lemma cpu_locks_lvl_at_intro (i : CPU) (n : nat) (lks : gset string) :
    (size lks <= n)%nat -> cpu_locks_at i lks -∗ cpu_locks_lvl_at i n lks.
  Proof. iIntros (Hsz) "H". iFrame "H". iPureIntro. exact Hsz. Qed.

  (* the level only ever needs WEAKENING upward (a push_off) *)
  Lemma cpu_locks_lvl_at_weaken (i : CPU) (n n' : nat) (lks : gset string) :
    (n <= n')%nat -> cpu_locks_lvl_at i n lks -∗ cpu_locks_lvl_at i n' lks.
  Proof. iIntros (Hle) "[H %Hsz]". iFrame "H". iPureIntro. lia. Qed.

End LockSet.

Section LockSetAmbient.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the ambient hart's held set -- the spelling every contract in the sconf
     tier uses, [cpu_hart] included. *)
  Definition cpu_locks (S : gset string) : iProp Σ := cpu_locks_at cpu_id S.

  Lemma cpu_locks_unfold (S : gset string) :
    cpu_locks S ⊣⊢ cpu_locks_at cpu_id S.
  Proof. reflexivity. Qed.

  (* the ambient-hart spelling of the level/set coupling *)
  Definition cpu_locks_lvl (n : nat) (S : gset string) : iProp Σ :=
    cpu_locks_lvl_at cpu_id n S.

  Lemma cpu_locks_lvl_elim (n : nat) (S : gset string) :
    cpu_locks_lvl n S -∗ cpu_locks S ∗ ⌜(size S <= n)%nat⌝.
  Proof. iApply cpu_locks_lvl_at_elim. Qed.

  Lemma cpu_locks_lvl_intro (n : nat) (S : gset string) :
    (size S <= n)%nat -> cpu_locks S -∗ cpu_locks_lvl n S.
  Proof. iIntros (H). iApply cpu_locks_lvl_at_intro. exact H. Qed.

  (* push_off raises the level; the coupling only ever needs WEAKENING *)
  Lemma cpu_locks_lvl_weaken (n n' : nat) (S : gset string) :
    (n <= n')%nat -> cpu_locks_lvl n S -∗ cpu_locks_lvl n' S.
  Proof. iIntros (Hle). iApply cpu_locks_lvl_at_weaken. exact Hle. Qed.

  (* RE-LEVEL the coupling: the only thing that ever changes is the level, and
     the new bound is supplied by whoever is moving it (push_off weakens for
     free, pop_off's caller states it).  Subsumes [cpu_locks_lvl_weaken]. *)
  Lemma cpu_locks_lvl_relevel (n n' : nat) (S : gset string) :
    (size S <= n')%nat -> cpu_locks_lvl n S -∗ cpu_locks_lvl n' S.
  Proof.
    iIntros (H) "H". iDestruct (cpu_locks_lvl_elim with "H") as "[H _]".
    iApply (cpu_locks_lvl_intro n' S H with "H").
  Qed.

  (* [n = 0] forces the set EMPTY -- the fact pop_off's re-enable branch and
     [cpu_own]'s [b = true] arm both want. *)
  Lemma cpu_locks_lvl_zero (S : gset string) :
    cpu_locks_lvl 0 S -∗ cpu_locks S ∗ ⌜S = ∅⌝.
  Proof.
    iIntros "H". iDestruct (cpu_locks_lvl_elim with "H") as "[$ %Hsz]".
    iPureIntro. apply leibniz_equiv, size_empty_inv. lia.
  Qed.

End LockSetAmbient.
