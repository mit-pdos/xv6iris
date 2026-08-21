(* ===================================================================== *)
(*  DirViewG.v -- THE PER-DIRECTORY CONTENTS GHOST [dview]                *)
(*  (claude-notes/projects/namei-pinned-lookup.md, N-1 / §9 W1)           *)
(* ===================================================================== *)

(*  WHAT IT IS.  A per-inum agreement on a directory's ABSTRACT CONTENTS --
    the first-match entry map [FsTree.dir_view] reads off the bytes -- filed
    under the ambient gname [IcacheRef.icfg_dview].  [icnt]'s vocabulary
    ([IcacheRef.icnt_at] .. [icnt_boot_split]) cloned at [gmap fname Z]; the
    proofs below are that section's, line for line, at [dfrac] instead of
    [Qp].

    WHY IT EXISTS.  The custody theorem (FsRep.v §1.4) says no thread can
    hold [fs_rep] over a tree, so the client-side carrier of "what the
    directory says" cannot be the fnode layer.  This is the one thing a
    client CAN hold beside the payload: a fragment the escrow does not own.
    N-3 lends it at a walk's hop instants; N-4 splits it into the pinned
    path.

    THE TIE IS DEFINITIONAL, NOT A GUARDED CONJUNCT (§9 Revision 1).  The
    abstract contents are a FUNCTION of state the payload already owns, so
    the custody chain carries [dv_hold z (dv_of dn data)] with no
    existential and no type guard.  Of a FILE the value is determined
    garbage that no client ever reads -- which is strictly cheaper than a
    [T_DIR]-guarded conjunct, because every byte-write re-pack then moves
    the ghost by one [dv_set] instead of re-proving a guard vacuous.

    THE WHOLE FRAGMENT RIDES THE CHAIN, AND THERE IS NO INVARIANT (§9
    Revision 2).  Half in an invariant would put that invariant in every
    write mover's context, which grows [SpecDirlink]/[SpecSysUnlink] by a
    premise, which propagates to the syscall tops and lands in [FsReady].
    Whole ownership instead makes [dv_set] a free own-update: no mask, no
    open, no landed contract's arity moved.  [dv_half] at a general [dfrac]
    exists for N-4's sake and has no consumer at this stage.

    KEY TYPE.  [dviewUR] is spelled over [list (bv 8)] because [Xv6Cameras]
    sits below [FsTree]; [FsTree.fname] IS that definition, so everything
    here states the theory at [fname] and the two spellings are convertible
    at every [own].                                                        *)

From Stdlib Require Import ZArith List FunctionalExtensionality.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import gmap dfrac updates.
From iris.algebra.lib Require Import dfrac_agree.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import own.
Require Import SailStdpp.Values.
Require Import DinodeEnc.   (* [dinode], [di_size]                        *)
Require Import DirView.     (* [dir_nrec]                                 *)
Require Import FsTree.      (* [fname], [dir_view]                        *)
Require Import IcacheRef.   (* [icfg_dview], [dview_boot_map]             *)

Section DirViewG.
  Context `{!icacheG Σ}.
  Context `{ICFG : icfg}.

  (* ===================================================================== *)
  (*  1.  THE FRAGMENT                                                      *)
  (* ===================================================================== *)

  Definition dv_half (z : Z) (dq : dfrac) (e : gmap fname Z) : iProp Σ :=
    own icfg_dview
        ({[ z := to_dfrac_agree dq (e : leibnizO (gmap fname Z)) ]} : dviewUR).

  (* THE ONLY SPELLING N-1 USES: the whole element, on the custody chain. *)
  Definition dv_hold (z : Z) (e : gmap fname Z) : iProp Σ :=
    dv_half z (DfracOwn 1) e.

  Global Instance dv_half_timeless z dq e : Timeless (dv_half z dq e).
  Proof. apply _. Qed.
  Global Instance dv_hold_timeless z e : Timeless (dv_hold z e).
  Proof. apply _. Qed.

  (* ===================================================================== *)
  (*  2.  THE TIE TO THE BYTES                                              *)
  (* ===================================================================== *)

  (* The record's size decides how many records the walk reads; the bytes
     decide what they say.  Both are the payload's own state, which is why
     no conjunct of the custody chain has to relate them. *)
  Definition dv_of (dn : dinode) (data : nat -> list (bv 8)) : gmap fname Z :=
    dir_view data (dir_nrec (bv_unsigned (di_size dn))).

  (* A RECORD MOVE THAT LEAVES [di_size] ALONE LEAVES THE CONTENTS ALONE.
     Every re-pack that touches only [di_type]/[di_nlink]/[di_addrs] --
     iupdate's link moves, the type fill, ialloc's retag -- closes its
     [dv_of] obligation by this and nothing else. *)
  Lemma dv_of_size (dn1 dn2 : dinode) (data : nat -> list (bv 8)) :
    di_size dn1 = di_size dn2 -> dv_of dn1 data = dv_of dn2 data.
  Proof. intros Hs. by rewrite /dv_of Hs. Qed.

  (* ...and the same fact as a RESOURCE move, which is the form the re-pack
     sites want: there the target record is fixed by the goal and only the
     size equation has to be supplied. *)
  Lemma dv_hold_size (z : Z) (dn1 dn2 : dinode) (data : nat -> list (bv 8)) :
    di_size dn1 = di_size dn2 ->
    dv_hold z (dv_of dn1 data) -∗ dv_hold z (dv_of dn2 data).
  Proof.
    intros Hs. rewrite (dv_of_size dn1 dn2 data Hs).
    iIntros "H". iExact "H".
  Qed.

  (* ...and the byte-side congruence, for a re-pack whose [data] is only
     EXTENSIONALLY the parked one (the writei tail's shape). *)
  Lemma dv_of_data (dn : dinode) (data1 data2 : nat -> list (bv 8)) :
    (forall k, data1 k = data2 k) -> dv_of dn data1 = dv_of dn data2.
  Proof.
    intros Hd. rewrite /dv_of.
    f_equal. apply functional_extensionality. exact Hd.
  Qed.

  (* ===================================================================== *)
  (*  3.  THE LAWS                                                          *)
  (* ===================================================================== *)

  (* AGREEMENT NEEDS NO OPEN AT ALL ([IcacheRef.icnt_agree]'s line), and at a
     general [dfrac] because N-4's lent fraction is what buys the pin. *)
  Lemma dv_agree (z : Z) (dq1 dq2 : dfrac) (e1 e2 : gmap fname Z) :
    dv_half z dq1 e1 -∗ dv_half z dq2 e2 -∗ ⌜e1 = e2⌝.
  Proof.
    rewrite /dv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    iPureIntro. by apply dfrac_agree_op_valid_L in Hv as [_ ->].
  Qed.

  (* THE MOVE IS FREE, and that is Revision 2's whole dividend: the holder of
     the payload is the sole holder of the element, so a byte-write moves the
     ghost with no mask, no invariant and no second party. *)
  Lemma dv_set (z : Z) (e e' : gmap fname Z) :
    dv_hold z e ==∗ dv_hold z e'.
  Proof.
    rewrite /dv_hold /dv_half. iIntros "H".
    iApply (own_update with "H").
    apply singleton_update, cmra_update_exclusive.
    split; done.
  Qed.

  (* SPLIT / JOIN at an arbitrary cut, for N-4.  No consumer at N-1. *)
  Lemma dv_split (z : Z) (dq1 dq2 : dfrac) (e : gmap fname Z) :
    dv_half z (dq1 ⋅ dq2) e ⊣⊢ dv_half z dq1 e ∗ dv_half z dq2 e.
  Proof.
    rewrite /dv_half -own_op singleton_op.
    by rewrite -dfrac_agree_op.
  Qed.

  Lemma dv_join (z : Z) (dq1 dq2 : dfrac) (e : gmap fname Z) :
    dv_half z dq1 e -∗ dv_half z dq2 e -∗ dv_half z (dq1 ⋅ dq2) e.
  Proof. iIntros "H1 H2". rewrite dv_split. iFrame. Qed.

  (* TWO HOLDS AT ONE INUM IS A REFUTATION -- the exclusivity that makes the
     hold a custody token rather than a claim. *)
  Lemma dv_hold_excl (z : Z) (e1 e2 : gmap fname Z) :
    dv_hold z e1 -∗ dv_hold z e2 -∗ False.
  Proof.
    rewrite /dv_hold /dv_half. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite singleton_op singleton_valid in Hv.
    by apply exclusive_l in Hv; [| apply to_dfrac_agree_exclusive].
  Qed.

  (* ===================================================================== *)
  (*  4.  THE BOOT MINT ([IcacheRef.icnt_boot_split]'s clone)               *)
  (* ===================================================================== *)

  (* [icfg_alloc]'s [DM] argument, taken apart: one WHOLE element per inum at
     the empty map, which is not the image's truth yet.  The stocking
     ([FsCfgBoot.ipool_alloc_of_image]) [dv_set]s each one to its own
     [dv_of] and parks it in the bundle it builds -- and it may do so in any
     order, because whole ownership answers to nobody. *)
  Lemma dv_boot_split (P : gset Z) :
    own icfg_dview (dview_boot_map P) ⊢ [∗ set] z ∈ P, dv_hold z ∅.
  Proof.
    rewrite /dview_boot_map
            (gset_to_gmap_singletons (A := dfrac_agreeR (leibnizO (gmap fname Z)))).
    rewrite big_opS_own_1. iIntros "H".
    iApply (big_sepS_mono with "H"). intros z _.
    iIntros "H". rewrite /dv_hold /dv_half. iExact "H".
  Qed.

End DirViewG.
