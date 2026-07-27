(* FdSlots.v -- the fd-slot resource: the capability that bounds how many
   references to one [struct file] can exist at once, and hence the reason
   xv6's unchecked [f->ref++] in filedup cannot overflow.

   The argument is a conservation law, and it is subtle enough to be worth
   spelling out:

     every holder of a reference to a struct file is a file descriptor of
     some process; there are at most NPROC processes and at most NOFILE
     descriptors each; NPROC * NOFILE is ~1000, which is nowhere near 2^31.

   Nothing in file.c enforces that -- it is a whole-kernel invariant -- so it
   has to be carried as a RESOURCE.  [fd_slot γ] is one unit of "somewhere to
   put a file reference".  The supply is fixed at [FDSLOTS] and minted once,
   at boot, by [fd_slots_alloc]; the proc layer distributes them to the
   NPROC * NOFILE descriptor slots.  A descriptor that names a file has GIVEN
   its slot away -- [ftable_res] holds one per outstanding reference (see
   FileInv.v) -- and gets it back when the descriptor is closed.  So

     (references to file k)  <=  (fd slots in existence)  =  FDSLOTS

   falls straight out of [own γ (● FDSLOTS)] against the fragments the table
   holds, with no arithmetic and no local update: the tokens for one slot are
   literally [◯ n], and [◯ n ⋅ ◯ 1 = ◯ (S n)].

   The resource lives here rather than in FileInv.v because it is a
   proc/fd-layer notion that the file table merely CONSUMES: the eventual
   [proc]-side model of [p->ofile[]] is the other end of the same law, and
   both sides should name the same thing. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list.
From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import ProcGeom.
Local Open Scope Z_scope.

(* param.h: open files per process.  (NPROC comes from ProcGeom.) *)
(* NOFILE now lives in ProcGeom.v with the rest of struct proc geometry. *)

(* The supply.  NOFILE descriptors per process, plus a small per-process
   allowance for the references a syscall holds in LOCALS while it has not
   yet installed them in a descriptor -- sys_open holds one between
   filealloc and fdalloc, pipealloc holds two.  Any comfortable constant
   below 2^31 would do; this one is the honest count. *)
Definition FDSLOTS : nat := (NPROC * (NOFILE + 4))%nat.

Definition fdslotUR : ucmra := authUR natUR.

Class fdslotG (Σ : gFunctors) := FdSlotG { fdslot_inG :: inG Σ fdslotUR }.
Definition fdslotΣ : gFunctors := #[GFunctor fdslotUR].
Global Instance subG_fdslotΣ {Σ} : subG fdslotΣ Σ -> fdslotG Σ.
Proof. solve_inG. Qed.

Section FdSlots.
  Context `{!fdslotG Σ}.

  (* [n] units of fd-slot capability.  [fd_slot γ] is one. *)
  Definition fd_slots (γ : gname) (n : nat) : iProp Σ := own γ (◯ n).
  Definition fd_slot (γ : gname) : iProp Σ := fd_slots γ 1.

  (* the fixed supply, held by whoever owns the accounting -- for files, the
     ftable lock's resource. *)
  Definition fd_slots_auth (γ : gname) : iProp Σ := own γ (● FDSLOTS).

  Global Instance fd_slots_timeless γ n : Timeless (fd_slots γ n).
  Proof. apply _. Qed.

  (* units split and merge freely: this is what lets a slot's [n] tokens sit
     in the table as one [◯ n] and still hand one back on close. *)
  Lemma fd_slots_op γ a b : fd_slots γ (a + b) ⊣⊢ fd_slots γ a ∗ fd_slots γ b.
  Proof.
    rewrite /fd_slots.
    assert (Hop : (◯ (a + b)%nat : fdslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma fd_slots_split γ a b : fd_slots γ (a + b) -∗ fd_slots γ a ∗ fd_slots γ b.
  Proof. rewrite fd_slots_op. iIntros "$". Qed.
  Lemma fd_slots_combine γ a b : fd_slots γ a -∗ fd_slots γ b -∗ fd_slots γ (a + b).
  Proof. iIntros "Ha Hb". rewrite fd_slots_op. iFrame. Qed.

  (* THE bound.  No update, no arithmetic: auth validity says the fragments
     in circulation cannot exceed the supply. *)
  Lemma fd_slots_bound γ n :
    fd_slots_auth γ -∗ fd_slots γ n -∗ ⌜(n <= FDSLOTS)%nat⌝.
  Proof.
    rewrite /fd_slots_auth /fd_slots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* ... and its consequence, the one filedup needs: a count that is backed
     by fd slots is far below what an [int] can hold, so incrementing it is
     safe.  This is where "there are only so many file descriptors" turns
     into "f->ref++ does not overflow". *)
  Lemma fd_slots_no_overflow γ (n : positive) :
    fd_slots_auth γ -∗ fd_slots γ (Pos.to_nat n) -∗
    ⌜(Z.pos n < 2 ^ 31)%Z /\ (Z.pos (Pos.succ n) < 2 ^ 31)%Z⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (fd_slots_bound with "Ha Hf") as %Hle.
    iPureIntro.
    assert (E31 : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
    assert (EF : FDSLOTS = 1280%nat) by (vm_compute; reflexivity).
    rewrite EF in Hle.
    assert (Hz : (Z.pos n <= 1280)%Z).
    { rewrite -positive_nat_Z. lia. }
    rewrite E31. lia.
  Qed.

  (* boot: mint the supply and hand every unit out.  The authority goes to
     the file table; the [FDSLOTS] units go to the proc layer, which parcels
     them out to the descriptor slots. *)
  Lemma fd_slots_alloc :
    ⊢ |==> ∃ γ, fd_slots_auth γ ∗ fd_slots γ FDSLOTS.
  Proof.
    iMod (own_alloc (● FDSLOTS ⋅ ◯ FDSLOTS)) as (γ) "[Ha Hf]".
    { apply auth_both_valid_discrete. split; [done | done]. }
    iModIntro. iExists γ. by iFrame.
  Qed.

  (* the parcelled-out form the proc layer wants *)
  Lemma fd_slots_to_list γ n :
    fd_slots γ n -∗ [∗ list] _ ∈ seq 0 n, fd_slot γ.
  Proof.
    induction n as [|n IH]; iIntros "H".
    - done.
    - rewrite seq_S big_sepL_app /=.
      replace (S n) with (n + 1)%nat by lia.
      iDestruct (fd_slots_split with "H") as "[Hn H1]".
      iSplitL "Hn"; [by iApply IH | by iFrame].
  Qed.

End FdSlots.
