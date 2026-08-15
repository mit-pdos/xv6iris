(* ProcAvail.v -- THE PROC TABLE'S TWO REGIMES, the [KallocInv] pattern for
   [struct proc proc[NPROC]] instead of for the page allocator.

   ---- WHY -------------------------------------------------------------

   [allocproc] scans the table for an UNUSED slot and returns 0 if it finds
   none.  Its caller [userinit] does NOT check the result -- it stores
   through the returned pointer immediately ([p->cwd = namei("/")], the
   [sd a0,336(s1)] at userinit+0x24) -- so a proof of userinit has to REFUTE
   the empty-table arm, and nothing in the proc table's own resources could
   express "some slot is UNUSED": [ProcGeom.pstate_lock] holds BOTH halves
   of the state mirror exactly when [unclaimed st = true], and
   [unclaimed UNUSED = true], so no fragment pinning a slot at UNUSED can
   exist outside that slot's lock.

   [kalloc] has the same shape and solves it with two regimes
   ([KallocInv.v]'s header): an EXCLUSIVE boot token asserting an exact free
   count -- under which allocation cannot fail -- and a PERSISTENT sealed
   witness carrying no count, under which it can.  This file is that, for
   the proc table.

   ---- THE MECHANISM ---------------------------------------------------

   The marker is on the ALLOCATED side, not the free side, and it is
   PERSISTENT.  [pslot_used j] is [own pav_name (◯ {[j]})] over
   [authUR (gsetUR nat)] -- core-idempotent, hence duplicable -- and it sits
   in [SchedCtx.proc_slots] on every arm except UNUSED.  Three consequences,
   and each is why this shape was chosen over the obvious "free token":

   1. A SCAN CAN ACCUMULATE IT.  allocproc releases each slot's lock before
      moving to the next, so an exclusive token read out of a slot would go
      straight back into the lock and the scan would end holding nothing.  A
      persistent one is kept, so after visiting all [NPROC] slots the scan
      holds [◯ (set_seq 0 NPROC)] -- and THAT is what the counted regime
      contradicts ([procs_avail_full]).

   2. NOBODY WHO MERELY PASSES A SLOT THROUGH HAS TO PAY.  Every state
      change except the two allocation ones goes through
      [SchedCtx.proc_slots_recast], which is restricted to
      [inv_dormant st = false] on both sides and therefore never crosses the
      UNUSED boundary: the conjunct is the same on both sides and the lemma
      is unchanged.  Only the sites that genuinely move a slot in or out of
      UNUSED -- allocproc and freeproc -- see it at all.

   3. THE AUTHORITY BOUNDS IT.  [● U] and [◯ {[j]}] give [j ∈ U], so
      [size (U ∩ [0,NPROC)) ≥ k] whenever [k] distinct slots are allocated,
      and [pav_free U] is what is left.

   ---- THE TWO REGIMES -------------------------------------------------

     [procs_avail (Some n)] -- BOOT.  The caller holds the authority [● U]
        itself, exclusively, together with [n <= pav_free U].  While anyone
        holds it no other thread can allocate or free a proc at all (a
        [None]-regime call needs the invariant below, and two [●] at one
        gname do not compose) -- the same "no concurrency during early boot"
        [KallocInv] formalizes.  With [Some (S k)], allocproc CANNOT return
        0.

     [procs_avail None] -- STEADY STATE.  The authority has moved into an
        invariant; the count is gone forever and allocproc may fail.
        Persistent, so every later caller threads it for free.
        [procs_avail_seal] converts [Some n ==∗ None] and there is no way
        back.

   Unlike [KallocInv] this needs no one-shot and no count ghost_var: the
   count lives in the caller's own authority, and sealing IS the move of
   that authority into the invariant.  Nothing ever re-enters the counted
   regime, which is what makes the simpler shape sound. *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import gmap gmultiset sets bitvector.definitions.
From iris.algebra Require Import auth gset.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own invariants.
Require Import SailStdpp.Base SailStdpp.Values SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto.
Require Import KallocInv.   (* [avail_dec] / [avail_sub] / [avail_zero] *)
Require Import ProcGeom.    (* [NPROC], [proc_addr] *)
Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The camera and the two classes.                                       *)
(*                                                                        *)
(*  [pavGpreS] is the FUNCTOR half -- an [inG], so the adequacy theorem    *)
(*  may assume it.  [pavG] carries the ghost NAME and therefore may not    *)
(*  be assumed: it is minted inside the boot fupd and handed out           *)
(*  EXISTENTIALLY, exactly as [InodeRef.iref_name_alloc] does for          *)
(*  [irefNameG] (durable-notes.md, "Typeclass sweeps").                    *)
(* ===================================================================== *)
Definition pavUR : ucmra := authUR (gsetUR nat).

Class pavGpreS (Σ : gFunctors) := {
  pav_pre_inG :: inG Σ pavUR;
}.
Definition pavΣ : gFunctors := #[GFunctor pavUR].
Global Instance subG_pavΣ {Σ} : subG pavΣ Σ -> pavGpreS Σ.
Proof. solve_inG. Qed.

Class pavG (Σ : gFunctors) := PavG {
  pavG_pre :: pavGpreS Σ;
  pav_name : gname;
}.

Definition pavN : namespace := nroot .@ "procavail".

(* the slots the table has, as a set -- the domain every count is taken in *)
Definition pav_region : gset nat := set_seq 0 NPROC.

(* how many slots are still free, given the allocated set *)
Definition pav_free (U : gset nat) : nat := (NPROC - size (U ∩ pav_region))%nat.

Lemma pav_region_size : size pav_region = NPROC.
Proof. rewrite /pav_region size_set_seq. reflexivity. Qed.

Lemma pav_free_empty : pav_free ∅ = NPROC.
Proof. rewrite /pav_free left_absorb_L size_empty. lia. Qed.

(* [size] is subadditive -- the one arithmetic fact [pav_free_add] rests on. *)
Lemma pav_size_union_le (X Y : gset nat) :
  (size (X ∪ Y) <= size X + size Y)%nat.
Proof.
  rewrite size_union_alt.
  assert (Hs : (size (Y ∖ X) <= size Y)%nat) by (apply subseteq_size; set_solver).
  lia.
Qed.

(* adding one slot costs at most one free slot -- the arithmetic
   [pslot_mint] needs, and the only place [size] is unfolded. *)
Lemma pav_free_add (U : gset nat) (j : nat) :
  (pav_free U - 1 <= pav_free (U ∪ {[j]}))%nat.
Proof.
  rewrite /pav_free.
  assert (Heq : (U ∪ {[j]}) ∩ pav_region
                = (U ∩ pav_region) ∪ ({[j]} ∩ pav_region)) by set_solver.
  rewrite Heq.
  pose proof (pav_size_union_le (U ∩ pav_region) ({[j]} ∩ pav_region)) as Hle.
  assert (Hone : (size ({[j]} ∩ pav_region) <= 1)%nat).
  { assert (Hss : {[j]} ∩ pav_region ⊆ ({[j]} : gset nat)) by set_solver.
    etransitivity; [ exact (subseteq_size _ _ Hss) | ].
    rewrite size_singleton. lia. }
  lia.
Qed.

(* a table whose every slot is allocated has no free slot left *)
Lemma pav_free_full (U : gset nat) : pav_region ⊆ U -> pav_free U = 0%nat.
Proof.
  intro Hsub. rewrite /pav_free.
  rewrite (_ : U ∩ pav_region = pav_region); [| set_solver].
  rewrite pav_region_size. lia.
Qed.

Section ProcAvail.
  Context `{!riscvGS Σ}.
  Context `{!pavG Σ}.

  (* ---- THE MARKER.  Persistent, so a scan keeps a copy of every slot it
     passes while handing the slot's own copy back with the lock. ---- *)
  Definition pslot_used (j : nat) : iProp Σ :=
    own pav_name (◯ ({[j]} : gset nat)).

  Global Instance pslot_used_persistent j : Persistent (pslot_used j).
  Proof. apply _. Qed.
  Global Instance pslot_used_timeless j : Timeless (pslot_used j).
  Proof. apply _. Qed.

  (* the marker at a slot named by its ADDRESS, which is the form
     [SchedCtx.proc_slots] can state (it is keyed on [pa], not on [j]). *)
  Definition pslot_used_at (pa : mword 64) : iProp Σ :=
    (∃ j : nat, ⌜pa = proc_addr j /\ (j < NPROC)%nat⌝ ∗ pslot_used j)%I.

  Global Instance pslot_used_at_persistent pa : Persistent (pslot_used_at pa).
  Proof. apply _. Qed.

  Lemma pslot_used_at_intro (j : nat) :
    (j < NPROC)%nat -> pslot_used j -∗ pslot_used_at (proc_addr j).
  Proof. iIntros (Hj) "H". iExists j. iFrame "H". done. Qed.

  Lemma pslot_used_at_elim (j : nat) :
    (j < NPROC)%nat -> pslot_used_at (proc_addr j) -∗ pslot_used j.
  Proof.
    iIntros (Hj) "(%k & [%Hpa %Hk] & H)".
    by rewrite (proc_addr_inj j k Hj Hk Hpa).
  Qed.

  (* ---- THE TWO REGIMES ---- *)
  Definition procs_avail (on : option nat) : iProp Σ :=
    match on with
    | Some n => ∃ U : gset nat, own pav_name (● U) ∗ ⌜(n <= pav_free U)%nat⌝
    | None   => inv pavN (∃ U : gset nat, own pav_name (● U))
    end%I.

  Global Instance procs_avail_None_persistent : Persistent (procs_avail None).
  Proof. apply _. Qed.

  (* boot -> steady state.  Irreversible: the authority goes into the
     invariant and the count is gone. *)
  Lemma procs_avail_seal (E : coPset) (n : nat) :
    procs_avail (Some n) ={E}=∗ procs_avail None.
  Proof.
    iIntros "(%U & Ha & _)".
    iApply (inv_alloc pavN E (∃ U : gset nat, own pav_name (● U))).
    iNext. iExists U. iFrame "Ha".
  Qed.

  (* WEAKENING the count -- what a caller with a budget to spare threads on. *)
  Lemma procs_avail_le (n m : nat) :
    (m <= n)%nat -> procs_avail (Some n) -∗ procs_avail (Some m).
  Proof.
    iIntros (Hle) "(%U & Ha & %Hn)". iExists U. iFrame "Ha". iPureIntro. lia.
  Qed.

  (* ---- THE REFUTATION.  This is the whole point of the counted regime:
     a scan that passed every slot holds every slot's marker, and a positive
     free count says it cannot have. ---- *)
  (* the markers of a LIST of slots, gathered into one fragment.  This is
     what persistence buys: each [pslot_used j] was duplicated out of slot
     [j]'s lock and handed back with it, and the copies compose. *)
  (* The markers of a LIST of slots, gathered ONTO the authority.  Seeding
     the induction with [● U] rather than with the unit is what keeps the
     base case a conversion instead of an update ([own_unit] is a [|==>]).
     This is what persistence buys: each [pslot_used j] was duplicated out
     of slot [j]'s lock and handed back with it, and the copies compose. *)
  Lemma pslot_used_gather (U : gset nat) (l : list nat) :
    own pav_name (● U) -∗
    ([∗ list] j ∈ l, pslot_used j) -∗
    own pav_name (● U ⋅ ◯ (list_to_set l : gset nat)).
  Proof.
    induction l as [|j l IH]; cbn [list_to_set].
    - iIntros "Ha _".
      assert (Hu : (◯ (∅ : gset nat) : pavUR) = ε) by reflexivity.
      rewrite Hu right_id. iExact "Ha".
    - iIntros "Ha [Hj Hl]".
      iDestruct (IH with "Ha Hl") as "H".
      iCombine "H Hj" as "H".
      rewrite -assoc -auth_frag_op gset_op.
      rewrite (_ : list_to_set l ∪ {[j]} = ({[j]} ∪ list_to_set l : gset nat));
        [| set_solver].
      iExact "H".
  Qed.

  Lemma pslot_used_all_auth (U : gset nat) :
    own pav_name (● U) -∗
    ([∗ list] j ∈ seq 0 NPROC, pslot_used j) -∗
    ⌜pav_region ⊆ U⌝.
  Proof.
    iIntros "Ha Hall".
    iDestruct (pslot_used_gather U (seq 0 NPROC) with "Ha Hall") as "H".
    rewrite list_to_set_seq.
    iDestruct (own_valid with "H") as %Hv%auth_both_valid_discrete.
    iPureIntro. destruct Hv as [Hincl _].
    rewrite /pav_region. by apply gset_included in Hincl.
  Qed.

  Lemma procs_avail_full (n : nat) :
    procs_avail (Some (S n)) -∗
    ([∗ list] j ∈ seq 0 NPROC, pslot_used j) -∗
    False.
  Proof.
    iIntros "(%U & Ha & %Hn) Hall".
    iDestruct (pslot_used_all_auth U with "Ha Hall") as %Hsub.
    rewrite (pav_free_full U Hsub) in Hn. lia.
  Qed.

  (* THE FORM THE ALLOCATOR'S EMPTY EXIT REPORTS, and [KallocInv]'s
     [kalloc_avail_zero] verbatim: a scan that passed every slot forces the
     caller's count, if it has one, to be 0.  The counted caller then
     refutes the whole arm from its own [Some (S k)] premise, and never
     sees it. *)
  Lemma procs_avail_zero (on : option nat) :
    ([∗ list] j ∈ seq 0 NPROC, pslot_used j) -∗
    procs_avail on -∗ ⌜avail_zero on⌝ ∗ procs_avail on.
  Proof.
    iIntros "#Hall Hav". destruct on as [n|]; [| by iFrame].
    destruct n as [|k]; [ by iFrame |].
    iExFalso. iApply (procs_avail_full k with "Hav Hall").
  Qed.


  (* ---- THE MINT.  Both regimes: the counted one updates the authority it
     holds, the sealed one opens the invariant. ---- *)
  Lemma pslot_mint_some (n j : nat) :
    procs_avail (Some n) ==∗ procs_avail (avail_dec (Some n)) ∗ pslot_used j.
  Proof.
    iIntros "(%U & Ha & %Hn)".
    iMod (own_update _ _ (● (U ∪ {[j]}) ⋅ ◯ ({[j]} ∪ U : gset nat)) with "Ha")
      as "[Ha Hf]".
    { apply auth_update_alloc.
      rewrite (_ : ({[j]} ∪ U) = (U ∪ {[j]} : gset nat)); [| set_solver].
      apply gset_local_update. set_solver. }
    iEval (rewrite -gset_op auth_frag_op own_op) in "Hf".
    iDestruct "Hf" as "[Hj _]".
    iModIntro. iSplitR "Hj"; [| iExact "Hj"].
    iExists (U ∪ {[j]}). iFrame "Ha". iPureIntro.
    cbn [avail_dec]. pose proof (pav_free_add U j). lia.
  Qed.

  Lemma pslot_mint_none (E : coPset) (j : nat) :
    ↑pavN ⊆ E ->
    procs_avail None ={E}=∗ pslot_used j.
  Proof.
    iIntros (HE) "#Hinv".
    iInv "Hinv" as (U) ">Ha" "Hclose".
    iMod (own_update _ _ (● (U ∪ {[j]}) ⋅ ◯ ({[j]} ∪ U : gset nat)) with "Ha")
      as "[Ha Hf]".
    { apply auth_update_alloc.
      rewrite (_ : ({[j]} ∪ U) = (U ∪ {[j]} : gset nat)); [| set_solver].
      apply gset_local_update. set_solver. }
    iEval (rewrite -gset_op auth_frag_op own_op) in "Hf".
    iDestruct "Hf" as "[Hj _]".
    iMod ("Hclose" with "[Ha]") as "_"; [iNext; iExists (U ∪ {[j]}); iFrame "Ha" |].
    iModIntro. iExact "Hj".
  Qed.

  (* the uniform statement the allocator's proof uses: at either regime the
     marker can be minted, and the count (if any) drops by one. *)
  Lemma pslot_mint (E : coPset) (on : option nat) (j : nat) :
    ↑pavN ⊆ E ->
    procs_avail on ={E}=∗ procs_avail (avail_dec on) ∗ pslot_used j.
  Proof.
    iIntros (HE) "Hav". destruct on as [n|].
    - iMod (pslot_mint_some n j with "Hav") as "[$ $]". done.
    - iDestruct "Hav" as "#Hav".
      iMod (pslot_mint_none E j HE with "Hav") as "Hu".
      iModIntro. iSplitR; [iExact "Hav" | iExact "Hu"].
  Qed.

End ProcAvail.

(* ===================================================================== *)
(*  BOOT: mint the ghost name and the whole table's worth of free slots.   *)
(*  OUTSIDE the section, over the FUNCTOR half only, because it is what    *)
(*  creates the name-carrying instance ([FdSlots.fd_slots_alloc]'s shape). *)
(* ===================================================================== *)
Lemma procs_avail_alloc `{!riscvGS Σ, !pavGpreS Σ} :
  ⊢ |==> ∃ _ : pavG Σ, procs_avail (Some NPROC).
Proof.
  iMod (own_alloc (● (∅ : gset nat))) as (γ) "Ha".
  { by apply auth_auth_valid. }
  iModIntro. iExists (PavG Σ _ γ). iExists ∅. iFrame "Ha".
  iPureIntro. rewrite pav_free_empty. lia.
Qed.
