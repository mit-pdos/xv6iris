(* FileOff.v -- [struct file]'s [off] field, and the BORROW PROTOCOL that
   owns it.  Design: claude-notes/design/file-table.md, "`off` -- staged".

   ---- WHY [off] IS NOT A CONTENT FIELD --------------------------------

   Three disciplines govern a [struct file]'s cells and the model keeps them
   apart (FileInv.v): [ref] is protected by ftable.lock; [type], [readable],
   [writable], [pipe], [ip] and [major] are immutable while [ref > 0] and so
   ride with a reference as ordinary points-to FRACTIONS; and [off] is
   neither.  [off] is MUTABLE, under [ip->lock], by a holder of an
   arbitrarily small fraction -- fileread does [f->off += r] holding
   whatever share its descriptor happens to have.  A fractional content
   field cannot express that: a write wants fraction one, and the last
   fraction is inside ftable.lock, which fileread never takes.

   So the cell lives HERE, in a permanent per-slot invariant, and is
   BORROWED across the instructions that use it.  The two obligations, from
   the design note:

     (a) a holder of ANY positive fraction of the reference, plus the
         inode's lock, may take the cell out across several instructions;
     (b) the EXCLUSIVE holder (q = 1) must be able to take it back with NO
         inode lock at all -- fileclose and sys_open reach [f->off] holding
         only ftable.lock.

   ---- WHAT MAKES (a) WORK, AND THE PIECE THE SKETCH WAS MISSING --------

   Mutual exclusion between two borrowers of one slot is the exclusivity of
   ONE INODE'S LOCK: both would have to hold [ip->lock] for the same [ip].
   To APPEAL to that, the invariant has to be able to say which inode it is
   talking about -- a per-slot invariant that only knows [k] cannot, and a
   borrower then has nothing to contradict a stale checked-out state with.
   (Two files can name two DIFFERENT inodes, so "some inode's lock is held"
   is not a contradiction.)

   The invariant therefore holds, permanently, HALF OF THE [f->ip] CELL.
   That is the cheapest possible record -- no ghost, no redundant copy of
   the pointer, and the arithmetic is invisible outside [FileInv.file_fields]
   (which holds the ip cell at half the nominal fraction for exactly this
   reason).  Points-to agreement then hands a reference holder
   "the invariant's inode is MY inode" for free.

   The MARKER a borrower parks is [i_valid ip ↦₄ 1]:

   * it is EXCLUSIVE and keyed by the INODE'S ADDRESS -- unlike
     [InodeLock.inode_locked] / [SleepLock.sleeplocked] / [inode_key], which
     are keyed by GHOST NAMES that a second borrower has no way to match;
   * it is FUNGIBLE -- [inode_locked] pins its value at 1, so what a
     borrower takes back on return is provably what it parked.  A slice of
     the borrower's own points-to fraction is NOT fungible (the invariant
     hands it back existentially quantified) which is why the marker cannot
     be one;
   * and readi / writei / iupdate do not touch [ip->valid], so a borrower
     can hold it out of [inode_locked] for the whole call.

   ---- WHAT MAKES (b) WORK ---------------------------------------------

   The exclusive holder has no inode lock, hence nothing to contradict the
   marker with.  What contradicts it is a COUNT: the checked-out disjunct
   also parks one unit of [FileInv.flive_tok], one of which exists per
   outstanding reference, with the authority beside the reference-count
   authority inside ftable.lock.  At the last reference the authority
   records ONE, so the parked unit cannot exist and the cell is resident
   ([FileInv.flive_excl_last]).  That holder's access is a SINGLE
   instruction ([f->off = 0], the [lw] of [ff = *f]), so it is an accessor
   rather than a borrow -- which is what it has to be, since it has no
   marker to park.

   ---- THE VALUE BOUND -------------------------------------------------

   The resident cell carries [off_wf]: an offset never exceeds
   MAXFILE*BSIZE.  This is not decoration.  readi's contract demands
   [off + n < 2^31] and NOTHING IN MEMORY bounds a freshly loaded [off], so
   without a bound in the invariant fileread cannot call readi at all.  The
   bound is inductive: the BSS starts zeroed, sys_open writes 0, and every
   advance is [off + r] with [r] clamped by readi/writei to the file's size,
   which is itself bounded by MAXFILE*BSIZE.  A pipe or device file never
   writes the cell. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions namespaces.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvExtras.
Require Import ArrCursor.
Require Import FdSlots.
Require Import WpLock.
Require Import PipeInv.
Require Import FileInv.
Require Import FsCrash.
Require Import InodeInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* one namespace, one invariant per slot *)
Definition offN : namespace := nroot .@ "fileoff".

(* the bound every stored offset satisfies -- see the header *)
Definition off_wf (v : mword 32) : Prop :=
  bv_unsigned v <= Z.of_nat MAXFILE * Z.of_nat BSIZE.

Lemma off_wf_zero : off_wf (mword_of_int 0 : mword 32).
Proof.
  rewrite /off_wf.
  assert (Hz : bv_unsigned (mword_of_int 0 : mword 32) = 0) by reflexivity.
  rewrite Hz. unfold MAXFILE, BSIZE. lia.
Qed.

(* an offset in range is BELOW int range, which is what makes the [lw] that
   loads it read the literal (and readi's [off + n < 2^31] premise
   dischargeable from a bound on [n] alone). *)
Lemma off_wf_lt31 (v : mword 32) : off_wf v -> bv_unsigned v < 2 ^ 31.
Proof.
  rewrite /off_wf. unfold MAXFILE, BSIZE. intro H.
  assert (E : (2 ^ 31 = 2147483648)%Z) by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(*  Timelessness of the two word points-tos this file puts in an invariant *)
(*  -- typeclass search does not unfold a [Definition] on its own, exactly *)
(*  as [RiscvPtsto.word4_pointsto_timeless]'s comment says.                *)
(* ---------------------------------------------------------------------- *)
Global Instance word_pointsto_timeless' `{!riscvGS Σ} (a : Arch.pa) (dq : dfrac)
    (w : bv 64) : Timeless (word_pointsto a dq w).
Proof. rewrite /word_pointsto. apply _. Qed.

Section FileOff.
  Context `{!riscvGS Σ, !lockG Σ, !fileG Σ, !fdslotG Σ}.

  (* ---- full ownership of a word is EXCLUSIVE ----
     [mem_pointsto_ne] at one address is a contradiction; that is all this
     is, and it is what refutes a stale marker / a stale resident cell. *)
  Lemma word4_pointsto_excl (a : Arch.pa) (dq : dfrac) (w1 w2 : bv 32) :
    a ↦₄ w1 -∗ a ↦₄{dq} w2 -∗ False.
  Proof.
    iIntros "H1 H2".
    rewrite !word4_pointsto_unfold.
    iDestruct "H1" as "[_ H1]". iDestruct "H2" as "[_ H2]".
    change (seq 0 4) with ([0; 1; 2; 3]%nat).
    iDestruct "H1" as "[Hb1 _]". iDestruct "H2" as "[Hb2 _]".
    iDestruct (mem_pointsto_ne with "Hb1 Hb2") as %Hne.
    iPureIntro. exact (Hne eq_refl).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  The invariant                                                      *)
  (* ------------------------------------------------------------------ *)

  Definition off_resident (k : nat) : iProp Σ :=
    (∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝)%I.

  (* the borrower's marker: the inode's [valid] flag, which [inode_locked]
     pins at 1 and which no fs.c callee below ilock touches. *)
  Definition off_mark (ip : mword 64) : iProp Σ :=
    (i_valid ip ↦₄ (mword_of_int 1 : mword 32))%I.

  Definition off_body (γ : gname) (k : nat) : iProp Σ :=
    (∃ ip : mword 64,
       a_fip k ↦₈{DfracOwn (1/2)%Qp} ip ∗
       (off_resident k ∨ (off_mark ip ∗ flive_tok γ k)))%I.

  Global Instance off_body_timeless γ k : Timeless (off_body γ k).
  Proof. rewrite /off_body /off_resident /off_mark. apply _. Qed.

  Definition off_inv (γ : gname) (k : nat) : iProp Σ :=
    inv (offN .@ k) (off_body γ k).

  Global Instance off_inv_persistent γ k : Persistent (off_inv γ k).
  Proof. apply _. Qed.

  (* the whole table's worth, as the boot wiring hands it out *)
  Definition off_invs (γ : gname) : iProp Σ :=
    ([∗ list] k ∈ seq 0 NFILE, off_inv γ k)%I.

  Global Instance off_invs_persistent γ : Persistent (off_invs γ).
  Proof. apply _. Qed.

  Lemma off_invs_lookup γ k :
    (k < NFILE)%nat -> off_invs γ -∗ off_inv γ k.
  Proof.
    iIntros (Hk) "H". rewrite /off_invs.
    assert (Hlk : seq 0 NFILE !! k = Some k) by (apply lookup_seq; lia).
    iDestruct (big_sepL_lookup (fun _ k => off_inv γ k) (seq 0 NFILE) k k Hlk
                 with "H") as "$".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  OBLIGATION (a): the borrow, under the inode's lock                  *)
  (* ------------------------------------------------------------------ *)

  (* CHECK OUT.  The [a_fip] share is only READ (agreement does not consume
     it) and comes straight back: it is the borrower's proof that the
     invariant's inode is the one whose lock it holds.  What is surrendered
     is the marker and one liveness unit. *)
  Lemma off_checkout (γ : gname) (k : nat) (dq : dfrac) (ip : mword 64)
      (E : coPset) :
    ↑(offN .@ k) ⊆ E ->
    off_inv γ k -∗ a_fip k ↦₈{dq} ip -∗ off_mark ip -∗ flive_tok γ k ={E}=∗
    a_fip k ↦₈{dq} ip ∗ ∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝.
  Proof.
    iIntros (HE) "#Hinv Hip Hmk Hlv".
    iMod (inv_acc _ _ _ HE with "Hinv") as "[>Hbody Hclose]".
    iDestruct "Hbody" as (ip') "[Hip' Hd]".
    iDestruct (word_pointsto_agree with "Hip Hip'") as %<-.
    iDestruct "Hd" as "[Hres | [Hmk' _]]"; last first.
    { iExFalso. iApply (word4_pointsto_excl with "Hmk Hmk'"). }
    iDestruct "Hres" as (v) "[Hc %Hwf]".
    iMod ("Hclose" with "[Hip' Hmk Hlv]") as "_".
    { iNext. iExists ip. iFrame "Hip'". iRight. iFrame. }
    iModIntro. iFrame "Hip". iExists v. iFrame. done.
  Qed.

  (* CHECK IN.  Holding the cell refutes the resident disjunct, so what
     comes back is the marker -- at the SAME value, [off_mark] being closed
     -- and the liveness unit. *)
  Lemma off_checkin (γ : gname) (k : nat) (dq : dfrac) (ip : mword 64)
      (v : mword 32) (E : coPset) :
    ↑(offN .@ k) ⊆ E ->
    off_wf v ->
    off_inv γ k -∗ a_fip k ↦₈{dq} ip -∗ a_foff k ↦₄ v ={E}=∗
    a_fip k ↦₈{dq} ip ∗ off_mark ip ∗ flive_tok γ k.
  Proof.
    iIntros (HE Hwf) "#Hinv Hip Hc".
    iMod (inv_acc _ _ _ HE with "Hinv") as "[>Hbody Hclose]".
    iDestruct "Hbody" as (ip') "[Hip' Hd]".
    iDestruct (word_pointsto_agree with "Hip Hip'") as %<-.
    iDestruct "Hd" as "[Hres | [Hmk Hlv]]".
    { iDestruct "Hres" as (v') "[Hc' _]".
      iExFalso. iApply (word4_pointsto_excl with "Hc Hc'"). }
    iMod ("Hclose" with "[Hip' Hc]") as "_".
    { iNext. iExists ip. iFrame "Hip'". iLeft. iExists v. iFrame. done. }
    iModIntro. iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  OBLIGATION (b): the exclusive holder, with no inode lock at all     *)
  (* ------------------------------------------------------------------ *)

  (* An ACCESSOR, not a borrow: the exclusive holder has no marker to park,
     so it may only hold the cell across ONE instruction -- which is all
     [f->off = 0] and the [lw] of [ff = *f] ever need.  The checked-out
     disjunct is refuted by the liveness count: at the last reference the
     authority records one unit and the holder has it. *)
  Lemma off_acc_excl (γ : gname) (M : gmap nat (Qp * positive)) (k : nat)
      (qt : Qp) (E : coPset) :
    ↑(offN .@ k) ⊆ E ->
    M !! k = Some (qt, 1%positive) ->
    off_inv γ k -∗ ftable_auth γ M -∗ flive_tok γ k
    ={E, E ∖ ↑(offN .@ k)}=∗
      ftable_auth γ M ∗ flive_tok γ k ∗
      (∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝) ∗
      (∀ v' : mword 32, ⌜off_wf v'⌝ -∗ a_foff k ↦₄ v'
         ={E ∖ ↑(offN .@ k), E}=∗ True).
  Proof.
    iIntros (HE HM) "#Hinv [Ha Hl] Hlv".
    assert (Hml : Mcount M !! k = Some 1%positive)
      by (rewrite Mcount_lookup HM; reflexivity).
    iMod (inv_acc _ _ _ HE with "Hinv") as "[>Hbody Hclose]".
    iDestruct "Hbody" as (ip) "[Hip Hd]".
    iDestruct "Hd" as "[Hres | [_ Hlv2]]"; last first.
    { iExFalso. iApply (flive_excl_last γ (Mcount M) k Hml with "Hl Hlv Hlv2"). }
    iDestruct "Hres" as (v) "[Hc %Hwf]".
    iModIntro. rewrite /ftable_auth. iFrame "Ha Hl Hlv".
    iSplitL "Hc". { iExists v. iFrame. done. }
    iIntros (v') "%Hwf' Hc'". iApply "Hclose". iNext.
    iExists ip. iFrame "Hip". iLeft. iExists v'. iFrame. done.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Boot: minting the invariants                                       *)
  (* ------------------------------------------------------------------ *)

  (* The cell and the ip cell's other half are what boot hands over; the BSS
     is zeroed, so [off_wf] holds of every slot at the start.  Nothing calls
     this yet, for the same reason nothing calls [ftable_ghosts_alloc]: the
     ftable lock is not wired at boot.  A resource nobody can MINT is a
     design hole that only surfaces when the wiring is written. *)
  Lemma off_inv_alloc (γ : gname) (k : nat) (v : mword 32) (ip : mword 64)
      (E : coPset) :
    off_wf v ->
    a_foff k ↦₄ v -∗ a_fip k ↦₈{DfracOwn (1/2)%Qp} ip ={E}=∗ off_inv γ k.
  Proof.
    iIntros (Hwf) "Hc Hip". rewrite /off_inv.
    iApply (inv_alloc (offN .@ k) E (off_body γ k)).
    iNext. iExists ip. iFrame "Hip". iLeft. iExists v. iFrame. done.
  Qed.

  Lemma off_invs_alloc (γ : gname) (vs : nat -> mword 32)
      (ips : nat -> mword 64) (E : coPset) :
    (forall k, off_wf (vs k)) ->
    ([∗ list] k ∈ seq 0 NFILE,
       a_foff k ↦₄ vs k ∗ a_fip k ↦₈{DfracOwn (1/2)%Qp} ips k) ={E}=∗
    off_invs γ.
  Proof.
    iIntros (Hwf) "H". rewrite /off_invs.
    iApply big_sepL_fupd.
    iApply (big_sepL_mono with "H"). intros i k Hk. iIntros "[Hc Hip]".
    iApply (off_inv_alloc γ k (vs k) (ips k) E (Hwf k) with "Hc Hip").
  Qed.

End FileOff.
