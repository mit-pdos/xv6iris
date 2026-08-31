(* FileOff.v -- the off LEDGER's protocol: publish, checkout, checkin.
   Design: claude-notes/projects/off-ledger.md (design of record until it
   lands in design/file-table.md).

   ---- WHY [off] IS NOT A CONTENT FIELD --------------------------------

   Three disciplines govern a [struct file]'s cells and the model keeps them
   apart (FileInvDefs.v): [ref] is protected by ftable.lock; [type],
   [readable], [writable], [pipe], [ip] and [major] are immutable while
   [ref > 0] and so ride with a reference as ordinary points-to FRACTIONS;
   and [off] is neither.  [off] is MUTABLE, under [ip->lock], by a holder of
   an arbitrarily small fraction -- fileread does [f->off += r] holding
   whatever share its descriptor happens to have.  A fractional content
   field cannot express that: a write wants fraction one, and the last
   fraction is inside ftable.lock, which fileread never takes.

   ---- THE LEDGER ------------------------------------------------------

   So ownership follows the inode: each ITABLE slot [i] carries a permanent
   per-era invariant, its off LEDGER ([FileInvDefs.ioff_escrow]), whose
   ghost map records WHICH file slots hold an FD_INODE reference on that
   inode, and which owns each member's [f->off] cell while it is resident.
   An FD_INODE reference carries a FRAGMENT of that map at its own fraction
   ([ioff_ref], inside [file_core]'s inode arm); every other file owns its
   cell directly ([foff_dead]).

   The four ownership transfers:

     ioff_publish   sys_open's FD_INODE arm, under [ip->lock]: deposit the
                    cell (freshly written 0), mint the fragment.
     ioff_checkout  fileread/filewrite's FD_INODE arm, under [ip->lock]:
                    take the cell out across the readi/writei window,
                    parking the MARKER and one liveness unit.
     ioff_checkin   the same window's end: the cell comes back (bound
                    re-proven), the marker and the unit come out.
     ioff_reclaim   fileclose's last-reference arm, under ftable.lock and
                    NO inode lock: spend the whole fragment, delete the
                    entry, take the cell back for the freed slot.  It
                    needs the liveness AUTHORITY, so it lives in FileInv.v.

   ---- WHAT MAKES THE ARMS RESOLVE -------------------------------------

   Mutual exclusion between two borrowers of one inode's cells is the
   exclusivity of THAT INODE'S LOCK, and the ledger can appeal to it
   directly because it is per-inode: the parked marker is
   [off_mark (ientry i)] = [i_valid (ientry i) ↦₄ 1], the valid cell only
   the sleeplock holder has (ilock hands it out at 1; readi/writei/iupdate
   never touch it).  It is EXCLUSIVE (two full points-tos at one address),
   ADDRESS-KEYED (no ghost name to fail to match) and CLOSED (pinned at 1,
   so what a borrower takes back is provably what it parked).  The
   publisher refutes stale membership the same two ways: a resident arm
   clashes with the cell it is about to deposit, a checked-out arm clashes
   with the marker it holds.

   The last closer holds neither cell nor lock; what it holds is the COUNT
   ([flive_tok], the ambient off-borrow liveness counter): at the last
   reference the authority inside ftable.lock records ONE unit, the closer
   has it, and the checked-out arm's parked unit would be a second --
   [FileInv.flive_excl_last].  That refutation reads the authority, so
   [ioff_reclaim] is FileInv.v's. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions namespaces.
From iris.algebra Require Import auth gmap frac numbers.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants own ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import FdSlots.
Require Import IcacheRef.   (* [ientry] -- the marker's address key *)
Require Import FileInvDefs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import IrefSlots.  (* [iref_frac] rides [file_core] -- FileInvDefs *)

Local Open Scope Z_scope.
Require Import TsoCtx.

Section FileOff.
  Context `{!riscvGS Σ, !xv6G Σ, !fileG Σ, !fdslotG Σ, !irefslotG Σ}.
  Context `{XI : CurCtx}.

  (* ------------------------------------------------------------------ *)
  (*  PUBLISH: sys_open's FD_INODE arm, under the inode's lock            *)
  (* ------------------------------------------------------------------ *)

  (* The marker is only the REFUTATION CREDENTIAL here (a stale checked-out
     arm would clash with it) and comes straight back; what is surrendered
     is the cell.  [k ∉ dom S] is not a premise -- the publisher PROVES it,
     from its own cell against the resident arm and its own marker against
     the checked-out one, which is exactly why membership needs no global
     bookkeeping. *)
  Lemma ioff_publish (E : coPset) (i k : nat) (v : mword 32) :
    ↑(offN .@ i) ⊆ E ->
    off_wf v ->
    ioff_escrow i -∗ off_mark (ientry i) -∗ a_foff k ↦₄ v ={E}=∗
    off_mark (ientry i) ∗ ioff_frag i k 1.
  Proof.
    iIntros (HE Hwf) "#Hinv Hmk Hc".
    rewrite /ioff_escrow.
    iMod (inv_acc with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as ">(%S & Ha & Hslots)".
    destruct (S !! k) as [[]|] eqn:HSk.
    { (* stale membership: both arms clash *)
      assert (Hdom : k ∈ dom S) by (apply elem_of_dom; by rewrite HSk).
      iDestruct (big_sepS_elem_of _ _ k Hdom with "Hslots") as "Hk".
      rewrite /ioff_slot_res.
      iDestruct "Hk" as "[Hres | [Hmk' _]]".
      - iDestruct "Hres" as (v') "[Hc' _]".
        iExFalso. iApply (word4_pointsto_excl with "Hc Hc'").
      - iExFalso. rewrite /off_mark.
        iApply (word4_pointsto_excl with "Hmk Hmk'"). }
    iMod (ghost_map_insert k () HSk with "Ha") as "[Ha Hfrag]".
    assert (Hnk : k ∉ dom S) by (by apply not_elem_of_dom).
    iMod ("Hclose" with "[Ha Hslots Hc]") as "_".
    { iApply bi.later_intro. iExists (<[k := ()]> S). iFrame "Ha".
      rewrite dom_insert_L (big_sepS_insert _ _ _ Hnk).
      iFrame "Hslots". iLeft. iExists v. iFrame. done. }
    iModIntro. iFrame "Hmk". rewrite /ioff_frag. iExact "Hfrag".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  CHECKOUT / CHECKIN: the borrow, under the inode's lock              *)
  (* ------------------------------------------------------------------ *)

  (* CHECK OUT.  The fragment proves membership (so the big-op HAS a slot
     for [k]); the marker refutes a stale checked-out arm; marker and one
     liveness unit are parked and the cell comes out, [off_wf] riding it.
     The fragment itself comes straight back -- it is only the membership
     witness -- which is what lets a borrower hand its whole [file_ref]
     back at the SAME fraction. *)
  Lemma ioff_checkout (E : coPset) (i k : nat) (q : Qp) :
    ↑(offN .@ i) ⊆ E ->
    ioff_escrow i -∗ ioff_frag i k q -∗ off_mark (ientry i) -∗ flive_tok k
    ={E}=∗
    ioff_frag i k q ∗ ∃ v : mword 32, a_foff k ↦₄ v ∗ ⌜off_wf v⌝.
  Proof.
    iIntros (HE) "#Hinv Hfrag Hmk Hlv".
    rewrite /ioff_escrow.
    iMod (inv_acc with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as ">(%S & Ha & Hslots)".
    iDestruct (ghost_map_lookup with "Ha Hfrag") as %HSk.
    assert (Hdom : k ∈ dom S) by (apply elem_of_dom; by rewrite HSk).
    iDestruct (big_sepS_delete _ _ k Hdom with "Hslots") as "[Hk Hrest]".
    rewrite {1}/ioff_slot_res.
    iDestruct "Hk" as "[Hres | [Hmk' _]]"; last first.
    { iExFalso. rewrite /off_mark.
      iApply (word4_pointsto_excl with "Hmk Hmk'"). }
    iDestruct "Hres" as (v) "[Hc %Hwf]".
    iMod ("Hclose" with "[Ha Hrest Hmk Hlv]") as "_".
    { iApply bi.later_intro. iExists S. iFrame "Ha".
      rewrite (big_sepS_delete _ _ k Hdom).
      iFrame "Hrest". iRight. iFrame. }
    iModIntro. iFrame "Hfrag". iExists v. iFrame. done.
  Qed.

  (* CHECK IN.  Holding the cell refutes the resident arm, so what comes
     back is the marker -- at the SAME value, [off_mark] being closed --
     and the liveness unit. *)
  Lemma ioff_checkin (E : coPset) (i k : nat) (q : Qp) (v : mword 32) :
    ↑(offN .@ i) ⊆ E ->
    off_wf v ->
    ioff_escrow i -∗ ioff_frag i k q -∗ a_foff k ↦₄ v ={E}=∗
    ioff_frag i k q ∗ off_mark (ientry i) ∗ flive_tok k.
  Proof.
    iIntros (HE Hwf) "#Hinv Hfrag Hc".
    rewrite /ioff_escrow.
    iMod (inv_acc with "Hinv") as "[Hbody Hclose]"; [exact HE|].
    iDestruct "Hbody" as ">(%S & Ha & Hslots)".
    iDestruct (ghost_map_lookup with "Ha Hfrag") as %HSk.
    assert (Hdom : k ∈ dom S) by (apply elem_of_dom; by rewrite HSk).
    iDestruct (big_sepS_delete _ _ k Hdom with "Hslots") as "[Hk Hrest]".
    rewrite {1}/ioff_slot_res.
    iDestruct "Hk" as "[Hres | [Hmk Hlv]]".
    { iDestruct "Hres" as (v') "[Hc' _]".
      iExFalso. iApply (word4_pointsto_excl with "Hc Hc'"). }
    iMod ("Hclose" with "[Ha Hrest Hc]") as "_".
    { iApply bi.later_intro. iExists S. iFrame "Ha".
      rewrite (big_sepS_delete _ _ k Hdom).
      iFrame "Hrest". iLeft. iExists v. iFrame. done. }
    iModIntro. iFrame.
  Qed.

End FileOff.
