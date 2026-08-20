(* FileOff.v -- the BORROW PROTOCOL over [struct file]'s [off] field.
   Design: claude-notes/design/file-table.md, "`off` -- staged".

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

   So the cell lives in a per-slot invariant and is BORROWED across the
   instructions that use it.  The two obligations, from the design note:

     (a) a holder of ANY positive fraction of the reference, plus the
         inode's lock, may take the cell out across several instructions;
     (b) the EXCLUSIVE holder (q = 1) must be able to take it back with NO
         inode lock at all -- fileclose and sys_open reach [f->off] holding
         only ftable.lock, or none.

   ---- WHERE THE INVARIANT LIVES, AND WHY IT IS CANCELLABLE ------------

   The definitions -- [off_resident], [off_mark], [off_body], [off_raw],
   [off_hold] and the [off_wf] bound -- are in FileInvDefs.v, beside
   [inode_pay], whose discipline they copy one field over.  THIS FILE IS THE
   PROTOCOL ONLY.

   The invariant is CANCELLABLE, AND UNARMED WHILE THE SLOT IS UNTYPED, and
   that pair is obligation (b)'s whole answer.  A permanent invariant cannot
   work: sys_open is the table's first WRITER of [f->ip] and [f->off], it
   holds the exclusive reference with ftable.lock RELEASED, and nothing it
   can hold refutes a stale checked-out disjunct -- [flive_tok] is
   fraction-free but composes, and any fractional witness the invariant could
   park comes back existentially quantified, which is not what its depositor
   needs (the thirteenth stop, fs-sysfile.md).  So the cinv an UNTYPED slot
   carries has no disjunction in its body at all, only the two cells: the
   publisher (sys_open, pipealloc) cancels it at fraction one, writes them
   with nothing in the way, mints an ARMED one with
   [FileInvDefs.off_hold_alloc] and records its name in [fpnames] with the
   same ghost step that installs the payload's.  [fileclose]'s
   last-reference arm cancels whichever it finds with
   [FileInv.off_hold_cancel] -- which is where obligation (b) is discharged,
   by the COUNT, inside the lock, with the authority -- and mints an unarmed
   one for the free slot it puts back.  A borrower opens the armed cinv at
   its own fraction, which rides [file_payload] proportionally as
   [FileInvDefs.off_hold].

   Consequence: there is NO fixed persistent family of off-invariants (a
   cancelled cinv cannot be re-armed at the same name, and the name changes
   on every publication), so no environment carries one.  A borrower reads
   the assertion out of its OWN reference --
   [SpecFileread.fileread_pay_carve] hands it out beside the inode share.
   Nothing about the off cell reaches [SpecFilealloc]'s post,
   [SpecFileclose]'s environment or [FileInvDefs.fslot]: a slot carries its
   cinv for its whole referenced life.

   ---- WHAT MAKES (a) WORK ---------------------------------------------

   Mutual exclusion between two borrowers of one slot is the exclusivity of
   ONE INODE'S LOCK: both would have to hold [ip->lock] for the same [ip].
   To APPEAL to that, the invariant has to be able to say which inode it is
   talking about -- a per-slot invariant that only knows [k] cannot, and a
   borrower then has nothing to contradict a stale checked-out state with.
   (Two files can name two DIFFERENT inodes, so "some inode's lock is held"
   is not a contradiction.)

   The body therefore holds, permanently, HALF OF THE [f->ip] CELL.  That is
   the cheapest possible record -- no ghost, no redundant copy of the
   pointer, and the arithmetic is invisible outside
   [FileInvDefs.file_fields] (which holds the ip cell at half the nominal
   fraction for exactly this reason).  Points-to agreement then hands a
   reference holder "the invariant's inode is MY inode" for free.

   The MARKER a borrower parks is [off_mark ip] = [i_valid ip ↦₄ 1]:

   * it is EXCLUSIVE and keyed by the INODE'S ADDRESS -- unlike
     [SleepLock.sleeplocked] / [IcacheEscrow.ic_tok], which are keyed by
     GHOST NAMES that a second borrower has no way to match;
   * it is FUNGIBLE -- a checked-out entry's valid cell is pinned at 1
     ([InodeLock.valid_word true]), so what a borrower takes back on return
     is provably what it parked.  A slice of the borrower's own points-to
     fraction is NOT fungible (the invariant hands it back existentially
     quantified) which is why the marker cannot be one;
   * and readi / writei / iupdate do not touch [ip->valid], so a borrower
     can hold it out of ilock's bundle for the whole call. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions namespaces.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own cancelable_invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import FdSlots.
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import IrefSlots.  (* [iref_frac] rides [file_core] -- FileInvDefs *)

Local Open Scope Z_scope.

Section FileOff.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.

  (* ------------------------------------------------------------------ *)
  (*  OBLIGATION (a): the borrow, under the inode's lock                  *)
  (* ------------------------------------------------------------------ *)

  (* CHECK OUT.  The [a_fip] share is only READ (agreement does not consume
     it) and comes straight back: it is the borrower's proof that the
     invariant's inode is the one whose lock it holds.  What is surrendered
     is the marker and one liveness unit.  The cinv token is likewise only
     an opening credential and comes back untouched -- which is what lets a
     borrower hand its whole [file_ref] back at the SAME fraction. *)
  Lemma off_checkout (γ γx : gname) (k : nat) (qc : Qp) (dq : dfrac)
      (ip : mword 64) (E : coPset) :
    ↑(offN .@ k) ⊆ E ->
    off_hold γ k γx true qc -∗ a_fip k ↦₈{dq} ip -∗ off_mark ip -∗
    flive_tok γ k ={E}=∗
    off_hold γ k γx true qc ∗ a_fip k ↦₈{dq} ip ∗
    ∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝.
  Proof.
    iIntros (HE) "[#Hinv Hoc] Hip Hmk Hlv".
    iMod (cinv_acc _ _ _ _ _ HE with "Hinv Hoc") as "(>Hbody & Hoc & Hclose)".
    iDestruct "Hbody" as (ip') "[Hip' Hd]".
    iDestruct (word_pointsto_agree with "Hip Hip'") as %<-.
    iDestruct "Hd" as "[Hres | [Hmk' _]]"; last first.
    { iExFalso. iApply (word4_pointsto_excl with "Hmk Hmk'"). }
    iDestruct "Hres" as (v) "[Hc %Hwf]".
    iMod ("Hclose" with "[Hip' Hmk Hlv]") as "_".
    { iNext. iExists ip. iFrame "Hip'". iRight. iFrame. }
    iModIntro. iFrame "Hinv Hoc Hip". iExists v. iFrame. done.
  Qed.

  (* CHECK IN.  Holding the cell refutes the resident disjunct, so what
     comes back is the marker -- at the SAME value, [off_mark] being closed
     -- and the liveness unit. *)
  Lemma off_checkin (γ γx : gname) (k : nat) (qc : Qp) (dq : dfrac)
      (ip : mword 64) (v : mword 32) (E : coPset) :
    ↑(offN .@ k) ⊆ E ->
    off_wf v ->
    off_hold γ k γx true qc -∗ a_fip k ↦₈{dq} ip -∗ a_foff k ↦₄ v
    ={E}=∗
    off_hold γ k γx true qc ∗ a_fip k ↦₈{dq} ip ∗ off_mark ip ∗ flive_tok γ k.
  Proof.
    iIntros (HE Hwf) "[#Hinv Hoc] Hip Hc".
    iMod (cinv_acc _ _ _ _ _ HE with "Hinv Hoc") as "(>Hbody & Hoc & Hclose)".
    iDestruct "Hbody" as (ip') "[Hip' Hd]".
    iDestruct (word_pointsto_agree with "Hip Hip'") as %<-.
    iDestruct "Hd" as "[Hres | [Hmk Hlv]]".
    { iDestruct "Hres" as (v') "[Hc' _]".
      iExFalso. iApply (word4_pointsto_excl with "Hc Hc'"). }
    iMod ("Hclose" with "[Hip' Hc]") as "_".
    { iNext. iExists ip. iFrame "Hip'". iLeft. iExists v. iFrame. done. }
    iModIntro. iFrame "Hinv Hoc". iFrame.
  Qed.

End FileOff.
