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
From iris.algebra Require Import auth numbers ufrac.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import ProcGeom.
Require Import FdSlots.   (* [NFILE]; NOT FileInv -- see FdSlots.v *)
Local Open Scope Z_scope.

(* references a single syscall may hold in locals at once; see the header *)
Definition IREFSPARE : nat := 4%nat.

(* THE BOOT CHAIN'S OWN TWO UNITS, and they are NOT part of the table's
   provisioning.  [SpecFsinit] takes one for ireclaim's iget/iput pair and
   [SpecKexec] -- which forkret's boot arm calls next off the same token --
   takes two; both run before any file is opened and neither hands anything
   back to the ftable.  If they were carved out of the [NFILE] units the
   table could not start with all [NFILE] slots FREE, and a free slot owns
   one whole unit ([FileInvDefs.file_core]'s untyped arm).  So they are their
   own row. *)
Definition IREFBOOT : nat := 2%nat.

(* one cwd per process, one per open file, plus the per-process allowance,
   plus the boot chain's two *)
Definition IREFSLOTS : nat := (NPROC * (1 + IREFSPARE) + NFILE + IREFBOOT)%nat.

(* THE CMRA IS FRACTIONAL, and it has to be.  A unit is evidence that the
   system has somewhere to put a reference, and for the [NFILE] units that
   somewhere is an ftable entry -- but an ftable entry's content is held at a
   FRACTION ([FileInvDefs.file_core] splits with [q], because filedup hands
   out shares of one file), so the unit backing it has to split the same way
   or it cannot live there at all.

   [ufracR] is [Qp] under [+] with no upper bound; [optionUR] adds the zero
   the auth needs as its unit.  The nat-indexed API below is unchanged and is
   what every existing caller still uses -- [iref_slots n] is [n] whole units
   -- with [iref_frac] the same resource read at an arbitrary share. *)
Definition irefslotUR : ucmra := authUR (optionUR ufracR).

(* [n] whole units, with zero as the cmra's own unit so that [iref_slots 0]
   is [emp]-like exactly as [◯ 0] was. *)
(* [optionUR ufracR], NOT [option ufrac]: [ufrac] is a Definition for [Qp]
   and Coq infers the BOUNDED [frac] camera for a bare [Qp] (see ufrac.v's
   own header), which is the wrong algebra and fails to unify silently. *)
Definition nat_ufrac (n : nat) : optionUR ufracR :=
  match n with
  | O    => None
  | S k  => Some (pos_to_Qp (Pos.of_succ_nat k))
  end.

Lemma nat_ufrac_1 : nat_ufrac 1 = Some 1%Qp.
Proof. reflexivity. Qed.

Lemma nat_ufrac_op (a b : nat) : nat_ufrac (a + b) = nat_ufrac a ⋅ nat_ufrac b.
Proof.
  destruct a as [|a]; destruct b as [|b]; cbn; try done.
  - by rewrite Nat.add_0_r.
  - rewrite -Some_op ufrac_op pos_to_Qp_add. do 2 f_equal. lia.
Qed.

(* the ORDER on whole units, which is what the supply bound turns into *)
Lemma nat_ufrac_incl (n m : nat) :
  nat_ufrac n ≼ nat_ufrac m -> (n <= m)%nat.
Proof.
  destruct n as [|n]; [lia|].
  destruct m as [|m]; cbn.
  - intros [z Hz]. destruct z; by inversion Hz.
  - intros Hincl.
    apply option_included in Hincl as [Hn | (x & y & Hx & Hy & Hxy)];
      [discriminate|].
    injection Hx as <-. injection Hy as <-.
    destruct Hxy as [Heq | Hlt].
    + apply leibniz_equiv in Heq. apply pos_to_Qp_inj in Heq. lia.
    + apply ufrac_included in Hlt.
      apply pos_to_Qp_inj_lt in Hlt. lia.
Qed.

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

  (* A SHARE of the supply.  [iref_frac 1] is one whole unit; a share below
     one is what an ftable entry's fraction of a file carries, and the shares
     of one entry always add back to the one unit that entry is provisioned
     for.  Nothing outside the file layer uses this reading. *)
  Definition iref_frac (q : Qp) : iProp Σ :=
    own irefslot_name (◯ (Some q : optionUR ufracR)).

  (* [n] units of iref-slot capability.  [iref_slot] is one. *)
  Definition iref_slots (n : nat) : iProp Σ := own irefslot_name (◯ nat_ufrac n).
  Definition iref_slot : iProp Σ := iref_slots 1.

  Lemma iref_slot_frac : iref_slot ⊣⊢ iref_frac 1.
  Proof. rewrite /iref_slot /iref_slots /iref_frac nat_ufrac_1. reflexivity. Qed.

  (* the fixed supply, held by the itable lock's resource *)
  Definition iref_slots_auth : iProp Σ :=
    own irefslot_name (● nat_ufrac IREFSLOTS).

  Global Instance iref_slots_timeless n : Timeless (iref_slots n).
  Proof. apply _. Qed.

  (* units split and merge freely: this is what lets a slot's [n] tokens sit
     in the table as one [◯ n] and still hand one back on iput. *)
  Lemma iref_slots_op a b : iref_slots (a + b) ⊣⊢ iref_slots a ∗ iref_slots b.
  Proof.
    rewrite /iref_slots nat_ufrac_op.
    assert (Hop : (◯ (nat_ufrac a ⋅ nat_ufrac b) : irefslotUR)
                  = ◯ nat_ufrac a ⋅ ◯ nat_ufrac b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  (* ---- and the same at an arbitrary share, which is what
     [FileInvDefs.file_core_split] needs ---- *)
  Lemma iref_frac_op q1 q2 : iref_frac (q1 + q2) ⊣⊢ iref_frac q1 ∗ iref_frac q2.
  Proof.
    rewrite /iref_frac.
    assert (Hop : (◯ (Some (q1 + q2)%Qp : optionUR ufracR) : irefslotUR)
                  = ◯ (Some q1 : optionUR ufracR) ⋅ ◯ (Some q2 : optionUR ufracR))
      by (rewrite -auth_frag_op -Some_op ufrac_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma iref_frac_split q1 q2 : iref_frac (q1 + q2) -∗ iref_frac q1 ∗ iref_frac q2.
  Proof. rewrite iref_frac_op. iIntros "$". Qed.
  Lemma iref_frac_combine q1 q2 : iref_frac q1 -∗ iref_frac q2 -∗ iref_frac (q1 + q2).
  Proof. iIntros "H1 H2". rewrite iref_frac_op. iFrame. Qed.

  Global Instance iref_frac_fractional : Fractional iref_frac.
  Proof. intros q1 q2. apply iref_frac_op. Qed.
  Global Instance iref_frac_as_fractional q :
    AsFractional (iref_frac q) iref_frac q.
  Proof. split; [reflexivity | apply _]. Qed.

  Global Instance iref_frac_timeless q : Timeless (iref_frac q).
  Proof. apply _. Qed.

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
    iPureIntro. by apply nat_ufrac_incl in Hincl.
  Qed.

  (* ... and its consequence, the one idup needs: a count backed by iref
     slots is far below what an [int] can hold, so incrementing it is safe.
     This is where "there are only so many places to keep an inode" turns
     into "ip->ref++ does not overflow". *)
  (* AT [positive], not [nat]: the count column of [Xv6Cameras.icacheUR] is
     [positiveR] (a live slot has at least one reference and the algebra
     has no zero).  The kfork line's [natR] retype of this statement is
     deferred with the rest of the count-0-share vocabulary -- see
     projects/reconcile-fork-icache.md, T5. *)
  Lemma iref_slots_no_overflow (n : positive) :
    iref_slots_auth -∗ iref_slots (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (iref_slots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EI : IREFSLOTS = 422%nat) by (vm_compute; reflexivity).
    rewrite EI in Hle.
    assert (Hz : (Z.pos n <= 422)%Z).
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
  iMod (own_alloc (● nat_ufrac IREFSLOTS ⋅ ◯ nat_ufrac IREFSLOTS)) as (γ) "[Ha Hf]".
  { apply auth_both_valid_discrete. split; [done | by destruct (nat_ufrac IREFSLOTS)]. }
  iModIntro. iExists (IrefSlotG Σ _ γ). by iFrame.
Qed.
