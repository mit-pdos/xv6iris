(* LockSet.v -- THE PER-CPU HELD-LOCK SET.

   Every hart owns a ghost set of the spinlocks it currently holds, named by
   their [struct spinlock]'s ADDRESS.  The authority rides in
   [IntrDefs.cpu_hart] -- with the running kernel thread while interrupts are
   off, inside [sie_arm true] while they are on -- and a lock whose [lk->cpu]
   field is SET keeps the matching fragment [lk_in i lk] inside its own
   invariant ([WpLock.lock_inv]).  So

       "lk->cpu = &cpus[i]"   and   "lk is in hart i's held set"

   are ONE fact, not two: the fragment cannot be forged and cannot be
   duplicated, and agreement against the authority reads the membership off it
   ([cpu_locks_in]).

   ---------------------------------------------------------------------
   WHY THE SET ALSO OWNS HALF OF [lk->cpu], AND WHY THAT IS THE WHOLE POINT

   [gset_disj] gives exclusivity and unforgeability, but minting a fragment
   needs [lk ∉ S] -- and acquire has no such precondition (nor should it yet:
   the deadlock discipline is a later phase).  What discharges it is the CPU
   FIELD ITSELF.  The set does not merely name the locks this hart holds; for
   each of them it OWNS HALF of that lock's [lk->cpu] cell, pinned at
   [cpus_ptr i] ([lk_stake]).  The lock's invariant holds the other half.
   Hence:

     - at acquire's [lk->cpu = mycpu()] the invariant still holds the cell
       WHOLE, at 0 (the lock is in the one-store window).  If [lk] were
       already in the set, the hart would be holding a half of that same cell
       at [cpus_ptr i] -- and [cpus_ptr i ≠ 0].  So [lk ∉ S] is DERIVED, from
       the very field the abstraction is about ([cpu_locks_fresh]).
     - at release's [lk->cpu = 0] the invariant holds only HALF, so the store
       is impossible until the hart gives its stake back -- which the
       fragment, via [cpu_locks_delete], is exactly the licence to do.

   This is the resource reading of the C code's own argument: a hart that
   already holds [lk] does not reach the store, because [acquire] runs
   [if(holding(lk)) panic()] first and panic never returns.  Here the
   panic-free path is not asserted, it is what the field ownership already
   says.

   ---------------------------------------------------------------------
   WHAT IS NOT HERE YET.  The set is HIDDEN: it rides inside [cpu_hart] under
   an existential, so no acquire/release/push_off/pop_off contract mentions
   it.  Exposing it as an index of [CpuOwn.cpu_own] -- which is what lets
   acquire demand [lk ∉ S], and later a lock ORDER -- is the next phase, and
   it is what makes "interrupts enabled implies the held set is empty"
   statable ([sie_arm true] carries [cpu_hart 0 true p], so the constraint
   lands there for free once [S] is an index). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import ProcGeom.   (* cpus_ptr and its injectivity/nonzero facts *)
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

  (* the authority: hart [i]'s held set.  Canonically named, so no contract
     carries a [γ] (RiscvPtsto.era_lockset_name). *)
  Definition lk_auth (i : CPU) (S : gset (mword 64)) : iProp Σ :=
    own (lockset_name i) (● (GSet S) : lockSetR).

  (* THE MEMBERSHIP FACT a lock with [lk->cpu] set keeps in its invariant. *)
  Definition lk_in (i : CPU) (lk : mword 64) : iProp Σ :=
    own (lockset_name i) (◯ (GSet {[lk]}) : lockSetR).

  (* the hart's STAKE in a held lock's cpu field: half the cell, pinned at
     its own [struct cpu].  The lock's invariant holds the other half. *)
  Definition lk_stake (i : CPU) (lk : mword 64) : iProp Σ :=
    (lock_cpu lk ↦₈{DfracOwn (1/2)} cpus_ptr i)%I.

  (* THE SET, as hart [i] owns it. *)
  Definition cpu_locks_at (i : CPU) (S : gset (mword 64)) : iProp Σ :=
    (lk_auth i S ∗ [∗ set] lk ∈ S, lk_stake i lk)%I.

  Global Instance lk_auth_timeless i S : Timeless (lk_auth i S).
  Proof. apply _. Qed.
  Global Instance lk_in_timeless i lk : Timeless (lk_in i lk).
  Proof. apply _. Qed.

  (* ---- the laws ------------------------------------------------------ *)

  (* THE TIE: the fragment a held lock keeps pins its address into the set. *)
  Lemma lk_in_agree (i : CPU) (S : gset (mword 64)) (lk : mword 64) :
    lk_auth i S -∗ lk_in i lk -∗ ⌜lk ∈ S⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply gset_disj_included in Hincl.
    apply singleton_subseteq_l in Hincl. exact Hincl.
  Qed.

  Lemma cpu_locks_in (i : CPU) (S : gset (mword 64)) (lk : mword 64) :
    cpu_locks_at i S -∗ lk_in i lk -∗ ⌜lk ∈ S⌝.
  Proof. iIntros "[Ha _] Hf". iApply (lk_in_agree with "Ha Hf"). Qed.

  (* the fragment is EXCLUSIVE -- two harts, or one hart twice, cannot both
     claim the same lock.  This is what makes the tie a fact about the
     machine rather than a decoration. *)
  Lemma lk_in_excl (i : CPU) (lk : mword 64) :
    lk_in i lk -∗ lk_in i lk -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op auth_frag_valid gset_disj_valid_op in Hv.
    (* [set_solver] is NOT usable over [gset (mword _)] -- see the note at the
       head of [cpu_locks_insert]. *)
    iPureIntro. apply disjoint_singleton_l in Hv.
    apply Hv, elem_of_singleton. reflexivity.
  Qed.

  (* THE DERIVATION acquire runs on: a cpu field that does not read
     [cpus_ptr i] cannot belong to a lock in hart [i]'s set, because the set
     would be holding a half of that very cell at [cpus_ptr i]. *)
  Lemma cpu_locks_stake_ne (i : CPU) (S : gset (mword 64)) (lk : mword 64)
      (dq : dfrac) (v : mword 64) :
    v <> cpus_ptr i ->
    cpu_locks_at i S -∗ lock_cpu lk ↦₈{dq} v -∗ ⌜lk ∉ S⌝.
  Proof.
    iIntros (Hne) "[_ Hst] Hcell".
    destruct (decide (lk ∈ S)) as [Hin | Hnin]; [| by iPureIntro ].
    iDestruct (big_sepS_elem_of _ _ lk Hin with "Hst") as "Hs".
    iDestruct (word_pointsto_agree with "Hcell Hs") as %Heq.
    exfalso. exact (Hne Heq).
  Qed.

  (* the instance acquire uses: the lock is in its one-store window, so the
     invariant still reads the field as 0 and holds it WHOLE. *)
  Lemma cpu_locks_fresh (i : CPU) (S : gset (mword 64)) (lk : mword 64)
      (dq : dfrac) :
    cpu_locks_at i S -∗ lock_cpu lk ↦₈{dq} (zero_reg : mword 64) -∗ ⌜lk ∉ S⌝.
  Proof.
    iIntros "Hcl Hcell".
    iApply (cpu_locks_stake_ne i S lk dq (zero_reg : mword 64) with "Hcl Hcell").
    apply eq_vec_false_iff. exact (cpus_ptr_nonzero i).
  Qed.

  (* acquire's ghost step, taken with the stake carved out of the cell the
     store has just written.

     TACTIC NOTE, and it bites anywhere a set over machine words appears:
     **[set_solver] does not work over [gset (mword n)]**.  It fails with
     "No matching clauses for match" -- not with an unsolved goal -- because
     its decision step runs on Sail's [Decidable_eq_mword] rather than
     stdpp's [bv_eq_dec] (the same instance divergence [riscvF_kmapGS] pins
     against in RiscvPtsto.v).  [set_unfold] alone is fine, and the same
     goals over [gset (bv n)] are fine.  Discharge membership/disjointness
     side conditions with the named lemmas instead
     ([disjoint_singleton_l], [singleton_subseteq_l], [elem_of_singleton]). *)
  Lemma cpu_locks_insert (i : CPU) (S : gset (mword 64)) (lk : mword 64) :
    lk ∉ S ->
    cpu_locks_at i S -∗ lk_stake i lk ==∗
    cpu_locks_at i ({[lk]} ∪ S) ∗ lk_in i lk.
  Proof.
    iIntros (Hnin) "[Ha Hst] Hs".
    assert (Hdisj : {[lk]} ## S) by (apply disjoint_singleton_l; exact Hnin).
    iMod (own_update _ _ ((● (GSet ({[lk]} ∪ S)) ⋅ ◯ (GSet {[lk]})) : lockSetR)
            with "Ha") as "[Ha Hf]".
    { apply auth_update_alloc.
      apply gset_disj_alloc_empty_local_update. exact Hdisj. }
    iModIntro. iFrame "Hf Ha".
    rewrite big_sepS_union; [| exact Hdisj ].
    rewrite big_sepS_singleton. iFrame "Hs Hst".
  Qed.

  (* release's ghost step: the fragment is the licence to take the stake
     back, which is what makes the [lk->cpu = 0] store possible at all. *)
  Lemma cpu_locks_delete (i : CPU) (S : gset (mword 64)) (lk : mword 64) :
    cpu_locks_at i S -∗ lk_in i lk ==∗
    ⌜lk ∈ S⌝ ∗ cpu_locks_at i (S ∖ {[lk]}) ∗ lk_stake i lk.
  Proof.
    iIntros "Hcl Hf".
    iDestruct (cpu_locks_in with "Hcl Hf") as %Hin.
    iDestruct "Hcl" as "[Ha Hst]".
    rewrite (big_sepS_delete _ S lk Hin).
    iDestruct "Hst" as "[Hs Hst]".
    iMod (own_update_2 _ _ _ ((● (GSet (S ∖ {[lk]}))) : lockSetR) with "Ha Hf")
      as "Ha".
    { apply auth_update_dealloc. apply gset_disj_dealloc_local_update. }
    iModIntro. iFrame "Hs Ha Hst". iPureIntro. exact Hin.
  Qed.

  (* boot: the authority arrives from adequacy at the empty set, with no
     stakes outstanding. *)
  Lemma cpu_locks_intro_empty (i : CPU) :
    lk_auth i ∅ -∗ cpu_locks_at i ∅.
  Proof. iIntros "Ha". iFrame "Ha". by rewrite big_sepS_empty. Qed.

End LockSet.

Section LockSetAmbient.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the ambient hart's held set -- the spelling every contract in the sconf
     tier uses, [cpu_hart] included. *)
  Definition cpu_locks (S : gset (mword 64)) : iProp Σ := cpu_locks_at cpu_id S.

  Lemma cpu_locks_unfold (S : gset (mword 64)) :
    cpu_locks S ⊣⊢ cpu_locks_at cpu_id S.
  Proof. reflexivity. Qed.

End LockSetAmbient.
