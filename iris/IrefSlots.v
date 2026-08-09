(* IrefSlots.v -- the FIXED SUPPLY that makes [ip->ref++] safe.

   idup increments [ip->ref] with no overflow check, exactly as filedup
   increments [f->ref].  The icache authority needs every count to stay a
   faithful [int] ([IcacheInv.icM_wf]'s second clause) -- that is what makes
   [ref == 0] mean "free" and what [IcacheInv.iref_word_live] turns into
   "ilock's [ref < 1] panic is dead" -- but

     forall n, Z.pos n < 2^31 -> Z.pos (Pos.succ n) < 2^31

   is FALSE at n = 2^31 - 1, so no unconditional increment can re-establish
   the bound and no axiom may assert that it does.  [SpecFiledup.v]'s header
   argues this at length; the argument is repeated here only because the
   conclusion is easy to forget when the counter is a different counter.

   The way out is [FdSlots.v]'s, verbatim in shape: an [authUR natUR] whose
   supply is a REAL, FINITE count of the places a reference can live.  A
   caller that wants to duplicate must hand in one unit, and a unit is
   evidence that the system has somewhere to put the new reference.  The
   accounting -- not arithmetic -- is what bounds the count.

   THE SUPPLY.  Where can an inode reference actually live?

     - each process's [p->cwd]                                    NPROC
     - each ftable entry holding an FD_INODE / FD_DEVICE file     NFILE
     - a per-process allowance for references a syscall holds in
       LOCALS before they reach either home            NPROC * IREFSPARE

   [IREFSPARE] is the honest count of simultaneous in-flight references, not
   a comfortable constant: [create] holds the parent directory and the new
   inode at once, and [link] holds [ip] and [dp] at once -- two.  Four is
   that with room, matching [FdSlots.FDSPARE]'s reasoning.

   Note this supply is NOT [FDSLOTS] and the two must not be shared: an fd
   slot bounds descriptors, an iref slot bounds inode references, and a
   process holds NOFILE of the first but at most one cwd of the second.

   Routing mirrors the fd units exactly: the AUTHORITY lives in the itable
   lock's resource ([IcacheInv.itable_res]) beside the per-slot counts, so
   that a thread holding the lock can weigh the count it is about to bump
   against the supply in one place.                                      *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import ProcGeom.
Require Import FileInv.
Local Open Scope Z_scope.

(* references a single syscall may hold in locals at once; see the header *)
Definition IREFSPARE : nat := 4%nat.

(* one cwd per process, one per open file, plus the per-process allowance *)
Definition IREFSLOTS : nat := (NPROC * (1 + IREFSPARE) + NFILE)%nat.

Definition irefslotUR : ucmra := authUR natUR.

(* As in [FdSlots], the ghost NAME lives in the class: there is exactly one
   iref-slot supply per system, and threading a [γ] would drag a filesystem
   ghost name through [ProcInv.proc_dormant] and every scheduler spec purely
   so that an empty cwd can hold a token. *)
Class irefslotGpreS (Σ : gFunctors) := { irefslot_pre_inG :: inG Σ irefslotUR }.
Class irefslotG (Σ : gFunctors) := IrefSlotG {
  irefslot_inG :: inG Σ irefslotUR;
  irefslot_name : gname;
}.
Global Instance irefslotG_preS `{!irefslotG Σ} : irefslotGpreS Σ :=
  {| irefslot_pre_inG := irefslot_inG |}.
Definition irefslotΣ : gFunctors := #[GFunctor irefslotUR].
Global Instance subG_irefslotΣ {Σ} : subG irefslotΣ Σ -> irefslotGpreS Σ.
Proof. solve_inG. Qed.

Section IrefSlots.
  Context `{!irefslotG Σ}.

  (* [n] units of iref-slot capability.  [iref_slot] is one. *)
  Definition iref_slots (n : nat) : iProp Σ := own irefslot_name (◯ n).
  Definition iref_slot : iProp Σ := iref_slots 1.

  (* the fixed supply, held by the itable lock's resource *)
  Definition iref_slots_auth : iProp Σ := own irefslot_name (● IREFSLOTS).

  Global Instance iref_slots_timeless n : Timeless (iref_slots n).
  Proof. apply _. Qed.

  (* units split and merge freely: this is what lets a slot's [n] tokens sit
     in the table as one [◯ n] and still hand one back on iput. *)
  Lemma iref_slots_op a b : iref_slots (a + b) ⊣⊢ iref_slots a ∗ iref_slots b.
  Proof.
    rewrite /iref_slots.
    assert (Hop : (◯ (a + b)%nat : irefslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma iref_slots_split a b : iref_slots (a + b) -∗ iref_slots a ∗ iref_slots b.
  Proof. rewrite iref_slots_op. iIntros "$". Qed.
  Lemma iref_slots_combine a b : iref_slots a -∗ iref_slots b -∗ iref_slots (a + b).
  Proof. iIntros "Ha Hb". rewrite iref_slots_op. iFrame. Qed.

  (* THE bound.  No update, no arithmetic: auth validity says the fragments
     in circulation cannot exceed the supply. *)
  Lemma iref_slots_bound n :
    iref_slots_auth -∗ iref_slots n -∗ ⌜(n <= IREFSLOTS)%nat⌝.
  Proof.
    rewrite /iref_slots_auth /iref_slots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* ... and its consequence, the one idup needs: a count backed by iref
     slots is far below what an [int] can hold, so incrementing it is safe.
     This is where "there are only so many places to keep an inode" turns
     into "ip->ref++ does not overflow". *)
  Lemma iref_slots_no_overflow (n : positive) :
    iref_slots_auth -∗ iref_slots (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (iref_slots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EI : IREFSLOTS = 420%nat) by (vm_compute; reflexivity).
    rewrite EI in Hle.
    assert (Hz : (Z.pos n <= 420)%Z).
    { rewrite -positive_nat_Z. lia. }
    rewrite E31. lia.
  Qed.

  (* ---- the boot-time distribution ----
     Stated exactly as [FdSlots]', and for the same reason: the proc layer
     parks units in [proc_dormant] and the file table parks one per entry,
     and both want the parcelled-out form. *)
  Lemma iref_slots_split_n (n m : nat) :
    iref_slots (n * m) -∗ [∗ list] _ ∈ seq 0 n, iref_slots m.
  Proof.
    induction n as [|n IH]; iIntros "H"; [done|].
    rewrite seq_S big_sepL_app /=.
    replace (S n * m)%nat with (m + n * m)%nat by lia.
    iDestruct (iref_slots_split with "H") as "[Hm Hn]".
    iSplitR "Hm"; [iApply IH; iFrame | iFrame].
  Qed.

  Lemma iref_slots_to_any {A} (l : list A) :
    iref_slots (length l) -∗ [∗ list] _ ∈ l, iref_slot.
  Proof.
    induction l as [|x l IH]; iIntros "H"; [done|].
    cbn [length big_opL].
    replace (S (length l)) with (length l + 1)%nat by lia.
    iDestruct (iref_slots_split with "H") as "[Hl H1]".
    iSplitL "H1"; [iFrame | iApply IH; iFrame].
  Qed.

  Lemma iref_slots_to_list n :
    iref_slots n -∗ [∗ list] _ ∈ seq 0 n, iref_slot.
  Proof.
    induction n as [|n IH]; iIntros "H".
    - done.
    - rewrite seq_S big_sepL_app /=.
      replace (S n) with (n + 1)%nat by lia.
      iDestruct (iref_slots_split with "H") as "[Hn H1]".
      iSplitL "Hn"; [iApply IH; iExact "Hn" | by iFrame].
  Qed.

End IrefSlots.

(* boot: mint the supply and hand every unit out.  CREATES the [irefslotG]
   instance, so it sits outside the section.  The authority goes to the
   itable; the IREFSLOTS units go to the proc and file layers. *)
Lemma iref_slots_alloc `{!irefslotGpreS Σ} :
  ⊢ |==> ∃ _ : irefslotG Σ, iref_slots_auth ∗ iref_slots IREFSLOTS.
Proof.
  iMod (own_alloc (● IREFSLOTS ⋅ ◯ IREFSLOTS)) as (γ) "[Ha Hf]".
  { apply auth_both_valid_discrete. split; [done | done]. }
  iModIntro. iExists (IrefSlotG Σ _ γ). by iFrame.
Qed.
