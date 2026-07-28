(* FdSlots.v -- the fd-slot resource: the capability that bounds how many
   references to one [struct file] can exist at once, and hence the reason
   xv6's unchecked [f->ref++] in filedup cannot overflow.

   The argument is a conservation law, and it is subtle enough to be worth
   spelling out:

     every holder of a reference to a struct file is a file descriptor of
     some process; there are at most NPROC processes and at most NOFILE
     descriptors each; NPROC * NOFILE is ~1000, which is nowhere near 2^31.

   Nothing in file.c enforces that -- it is a whole-kernel invariant -- so it
   has to be carried as a RESOURCE.  [fd_slot] is one unit of "somewhere to
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

(* The per-process ALLOWANCE: units for the references a syscall holds in
   LOCALS while they have not yet reached a descriptor.  sys_open holds one
   between filealloc and fdalloc; sys_pipe holds two (SpecSysPipe.v takes them
   as premises and returns both on every one of its four exits).  Any
   comfortable constant would do; this one is the honest count.

   It is routed exactly like the per-descriptor units: procinit parks it in
   each process's [ProcInv.proc_dormant], allocproc takes it out with the
   block, and it travels ALONGSIDE [proc_priv] for a live process -- not
   inside it.  Beside rather than inside because [proc_priv]'s accessors all
   have the borrow-and-return shape, whose wand swallows the block: a syscall
   that held its allowance *out* of [proc_priv] could not then pass
   [proc_priv] to a callee, which is precisely what sys_pipe does. *)
Definition FDSPARE : nat := 4%nat.

(* The supply: NOFILE descriptors plus the allowance, per process. *)
Definition FDSLOTS : nat := (NPROC * (NOFILE + FDSPARE))%nat.

Definition fdslotUR : ucmra := authUR natUR.

(* The ghost NAME lives in the class, not in every predicate that mentions a
   slot.  There is exactly one fd-slot supply per system, and the alternative
   -- a [γs] parameter -- would drag a filesystem ghost name through
   [ProcInv.proc_dormant], hence [SchedCtx.proc_slots], [proc_lock_res] and
   every scheduler spec, purely so that an EMPTY descriptor can hold a token.
   That is the leakage SpecArgraw.v already argues against for [γf]. *)
Class fdslotGpreS (Σ : gFunctors) := { fdslot_pre_inG :: inG Σ fdslotUR }.
Class fdslotG (Σ : gFunctors) := FdSlotG {
  fdslot_inG :: inG Σ fdslotUR;
  fdslot_name : gname;
}.
Global Instance fdslotG_preS `{!fdslotG Σ} : fdslotGpreS Σ :=
  {| fdslot_pre_inG := fdslot_inG |}.
Definition fdslotΣ : gFunctors := #[GFunctor fdslotUR].
Global Instance subG_fdslotΣ {Σ} : subG fdslotΣ Σ -> fdslotGpreS Σ.
Proof. solve_inG. Qed.

Section FdSlots.
  Context `{!fdslotG Σ}.

  (* [n] units of fd-slot capability.  [fd_slot] is one. *)
  Definition fd_slots (n : nat) : iProp Σ := own fdslot_name (◯ n).
  Definition fd_slot : iProp Σ := fd_slots 1.

  (* the fixed supply, held by whoever owns the accounting -- for files, the
     ftable lock's resource. *)
  Definition fd_slots_auth : iProp Σ := own fdslot_name (● FDSLOTS).

  Global Instance fd_slots_timeless n : Timeless (fd_slots n).
  Proof. apply _. Qed.

  (* units split and merge freely: this is what lets a slot's [n] tokens sit
     in the table as one [◯ n] and still hand one back on close. *)
  Lemma fd_slots_op a b : fd_slots (a + b) ⊣⊢ fd_slots a ∗ fd_slots b.
  Proof.
    rewrite /fd_slots.
    assert (Hop : (◯ (a + b)%nat : fdslotUR) = ◯ a ⋅ ◯ b)
      by (rewrite -auth_frag_op; reflexivity).
    rewrite Hop own_op. reflexivity.
  Qed.

  Lemma fd_slots_split a b : fd_slots (a + b) -∗ fd_slots a ∗ fd_slots b.
  Proof. rewrite fd_slots_op. iIntros "$". Qed.
  Lemma fd_slots_combine a b : fd_slots a -∗ fd_slots b -∗ fd_slots (a + b).
  Proof. iIntros "Ha Hb". rewrite fd_slots_op. iFrame. Qed.

  (* THE bound.  No update, no arithmetic: auth validity says the fragments
     in circulation cannot exceed the supply. *)
  Lemma fd_slots_bound n :
    fd_slots_auth -∗ fd_slots n -∗ ⌜(n <= FDSLOTS)%nat⌝.
  Proof.
    rewrite /fd_slots_auth /fd_slots. iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply nat_included in Hincl.
  Qed.

  (* ... and its consequence, the one filedup needs: a count that is backed
     by fd slots is far below what an [int] can hold, so incrementing it is
     safe.  This is where "there are only so many file descriptors" turns
     into "f->ref++ does not overflow". *)
  Lemma fd_slots_no_overflow (n : positive) :
    fd_slots_auth -∗ fd_slots (Pos.to_nat n) -∗
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

  (* ---- the boot-time distribution ----
     procinit hands each of the NPROC processes NOFILE units, one per
     descriptor.  Stated over an arbitrary [n * m] because that is all the
     induction needs, and over an arbitrary LIST at the leaf because
     [proc_dormant] pairs its units with [pv_ofile V], whose elements are
     irrelevant -- only its length is. *)
  Lemma fd_slots_split_n (n m : nat) :
    fd_slots (n * m) -∗ [∗ list] _ ∈ seq 0 n, fd_slots m.
  Proof.
    induction n as [|n IH]; iIntros "H"; [done|].
    rewrite seq_S big_sepL_app /=.
    replace (S n * m)%nat with (m + n * m)%nat by lia.
    iDestruct (fd_slots_split with "H") as "[Hm Hn]".
    iSplitR "Hm"; [iApply IH; iFrame | iFrame].
  Qed.

  Lemma fd_slots_to_any {A} (l : list A) :
    fd_slots (length l) -∗ [∗ list] _ ∈ l, fd_slot.
  Proof.
    induction l as [|x l IH]; iIntros "H"; [done|].
    cbn [length big_opL].
    replace (S (length l)) with (length l + 1)%nat by lia.
    iDestruct (fd_slots_split with "H") as "[Hl H1]".
    iSplitL "H1"; [iFrame | iApply IH; iFrame].
  Qed.

  (* the parcelled-out form the proc layer wants *)
  Lemma fd_slots_to_list n :
    fd_slots n -∗ [∗ list] _ ∈ seq 0 n, fd_slot.
  Proof.
    induction n as [|n IH]; iIntros "H".
    - done.
    - rewrite seq_S big_sepL_app /=.
      replace (S n) with (n + 1)%nat by lia.
      iDestruct (fd_slots_split with "H") as "[Hn H1]".
      iSplitL "Hn"; [iApply IH; iExact "Hn" | by iFrame].
  Qed.

End FdSlots.

(* boot: mint the supply and hand every unit out.  This CREATES the [fdslotG]
   instance, so it sits outside the section -- before the name exists only the
   [pre] class is available.  The authority goes to the file table; the
   FDSLOTS units go to the proc layer, which parcels them out to the
   descriptor slots ([fd_slots_to_list]). *)
Lemma fd_slots_alloc `{!fdslotGpreS Σ} :
  ⊢ |==> ∃ _ : fdslotG Σ, fd_slots_auth ∗ fd_slots FDSLOTS.
Proof.
  iMod (own_alloc (● FDSLOTS ⋅ ◯ FDSLOTS)) as (γ) "[Ha Hf]".
  { apply auth_both_valid_discrete. split; [done | done]. }
  iModIntro. iExists (FdSlotG Σ _ γ). by iFrame.
Qed.
