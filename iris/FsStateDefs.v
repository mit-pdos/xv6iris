(* FsStateDefs.v -- the view record [Γ], the byte points-to, and the two
   block-level shapes every other file-system predicate is built from.

   Design of record: claude-notes/design/fs-state.md sections 0-2.  This is
   stage 2a of claude-notes/projects/durable-disk.md.

   THE ONE THING THAT MENTIONS A DISK is the field [fsΦ] of [fs_view_names]:
   a byte-address-keyed points-to, ABSTRACT here.  The file system is
   instantiated twice over the same definitions (fs-state.md section 1) --
   at the committed view [Γ_D], where [fsΦ] is the full element of the
   fixed-layer byte map, and at the logged view [Γ_L], where it is the full
   element of the era's logged view.  Nothing below knows which.

   Consequently this file imports NOTHING from [FsBlocks]/[LogInv]/any
   [Proof*]/[Spec*] file: it is pure Iris over the tree's ENCODING
   vocabulary (FsImg/DinodeEnc/BitmapEnc/FsTree/BlockWords) only.

   THE POINTS-TO IS FRACTION-INDEXED (durable-fs-plan.md sections 4 and 6,
   lane B').  [fsΦ] takes a [dfrac], and so do the two block shapes, in the
   [_q] forms below; [byte_range] and [blk_owned] are the [DfracOwn 1]
   READINGS of them and their text has not moved, which is why the durable
   instance (FsDurBytes/FsDurImg/FsDurObj/FsDurSnap/FsDurLedger and
   FsStateBitmap -- about seventy-five uses, all at fraction 1 by plan
   section 1) is untouched by the index.  What wants a fraction is exactly
   the ERA instance's data and indirect blocks, so that [ilock] without a
   transaction can hand a reader a QUARTER (plan section 4: two read-locked
   inodes leaving three quarters each cannot alias a block, 3/4 + 3/4 > 1,
   so cross-inode disjointness at the commit's collection stays pure
   separation logic).  RECORDS DO NOT: they park region-side at fraction 1
   always, so [rec_owned] keeps its arity.

   Three properties of [fsΦ] are needed by consumers and cannot be proved of
   an abstract predicate, so they are stated here and TAKEN AS PARAMETERS
   where they are used (the standing rule: a parameter, not a new
   config-class dependency):

   - [phi_excl Γ]: two owners of one byte own no more than all of it, i.e.
     [fsΦ dq1 ∗ fsΦ dq2 ⊢ ✓ (dq1 ⋅ dq2)].  Its fraction-1 reading is the
     old "two owners is [False]", which is what makes [free_bitmap]'s "the
     bit reads allocated" argument run (fs-state.md section 2) -- the
     [fsblock_excl] of the concrete instance, lifted; its 3/4 + 3/4 reading
     is the commit's cross-inode disjointness.
   - [phi_frac Γ]: the points-to splits along [⋅], which is how a quarter
     is handed out and taken back.
   - [GTimeless Γ]: every byte points-to is timeless.  Both concrete
     instances are ghost-map elements, so both satisfy it, and every
     predicate below is then timeless -- which is what the [>]-strips of
     the in-memory accessors need (fs-ghost-state.md section 1).  *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop.
Require Import BioDefs.
Require Import FsImg.

(* the proofmode import re-opens nat_scope on top of the scope stack, so the
   file's scope has to be (re-)issued after it -- durable-notes.md *)
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The view record                                                *)
(* ------------------------------------------------------------------ *)

Section GammaDefs.
  Context {Σ : gFunctors}.

  (* [fsΦ] is spelled [Φ] in the design; the field is renamed here because a
     top-level projection named [Φ] would shadow the proofmode's ubiquitous
     [Φ] binder at every use site. *)
  Record fs_view_names := MkFsView {
    fsΦ   : dfrac -> Z -> bv 8 -> iProp Σ;  (* byte ownership, BY BYTE ADDRESS *)
    γlink : gname;                  (* the link-counting family (FsStateLink) *)
    γtop  : gname;                  (* the top-level abstract map (FsState)   *)
  }.

  (* the exclusivity law of the concrete instances, as a hypothesis.  The
     fraction-aware form: two owners of one byte hold a VALID sum.  At
     [DfracOwn 1] on either side that sum is invalid, which is the old
     law; at [3/4 ⋅ 3/4] it is invalid too, which is why a read-locker's
     share is a quarter and not a half (plan section 4). *)
  Definition phi_excl (Γ : fs_view_names) : Prop :=
    forall (a : Z) (v w : bv 8) (dq1 dq2 : dfrac),
      (fsΦ Γ dq1 a v ∗ fsΦ Γ dq2 a w) ⊢ ⌜✓ (dq1 ⋅ dq2)⌝.

  (* ...and the splitting law, which is how the quarter is handed out.
     Stated on [DfracOwn] alone -- that is the [Fractional] law both
     ghost-map instances satisfy, and every share the design hands out is
     an ordinary fraction. *)
  Definition phi_frac (Γ : fs_view_names) : Prop :=
    forall (a : Z) (v : bv 8) (q1 q2 : Qp),
      fsΦ Γ (DfracOwn (q1 + q2)) a v
      ⊣⊢ fsΦ Γ (DfracOwn q1) a v ∗ fsΦ Γ (DfracOwn q2) a v.

  Class GTimeless (Γ : fs_view_names) :=
    gtimeless : forall (dq : dfrac) (a : Z) (v : bv 8), Timeless (fsΦ Γ dq a v).

  (* ---------------------------------------------------------------- *)
  (*  2.  The points-to run                                            *)
  (* ---------------------------------------------------------------- *)

  (* [bs] resides at byte offset [off] of block [b], at share [dq]. *)
  Definition byte_range_q (Γ : fs_view_names) (dq : dfrac) (b off : Z)
      (bs : list (bv 8)) : iProp Σ :=
    ([∗ list] k ↦ v ∈ bs, fsΦ Γ dq (b * BSIZE_z + off + Z.of_nat k) v)%I.

  (* THE FRACTION-1 READING, and it is a [Definition] rather than a
     notation so that every one of the ~75 durable-side uses and every
     [rewrite /blk_owned] in the tree keeps its exact text. *)
  Definition byte_range (Γ : fs_view_names) (b off : Z) (bs : list (bv 8))
    : iProp Σ :=
    byte_range_q Γ (DfracOwn 1) b off bs.

  (* a whole block, at its full width, at share [dq] *)
  Definition blk_owned_q (Γ : fs_view_names) (dq : dfrac) (b : Z)
      (bs : list (bv 8)) : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range_q Γ dq b 0 bs)%I.

  Definition blk_owned (Γ : fs_view_names) (b : Z) (bs : list (bv 8))
    : iProp Σ :=
    (⌜length bs = BSIZE⌝ ∗ byte_range Γ b 0 bs)%I.

  Lemma byte_range_1 Γ b off bs :
    byte_range Γ b off bs = byte_range_q Γ (DfracOwn 1) b off bs.
  Proof. reflexivity. Qed.

  Lemma blk_owned_1 Γ b bs :
    blk_owned Γ b bs = blk_owned_q Γ (DfracOwn 1) b bs.
  Proof. reflexivity. Qed.

  Global Instance byte_range_q_timeless `{!GTimeless Γ} dq b off bs :
    Timeless (byte_range_q Γ dq b off bs).
  Proof.
    rewrite /byte_range_q. apply big_sepL_timeless.
    intros. apply gtimeless.
  Qed.

  Global Instance byte_range_timeless `{!GTimeless Γ} b off bs :
    Timeless (byte_range Γ b off bs).
  Proof. rewrite /byte_range. apply _. Qed.

  Global Instance blk_owned_q_timeless `{!GTimeless Γ} dq b bs :
    Timeless (blk_owned_q Γ dq b bs).
  Proof. rewrite /blk_owned_q. apply _. Qed.

  Global Instance blk_owned_timeless `{!GTimeless Γ} b bs :
    Timeless (blk_owned Γ b bs).
  Proof. rewrite /blk_owned. apply _. Qed.

  Lemma blk_owned_q_length Γ dq b bs :
    blk_owned_q Γ dq b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma blk_owned_length Γ b bs : blk_owned Γ b bs -∗ ⌜length bs = BSIZE⌝.
  Proof. iIntros "[% _]". done. Qed.

  Lemma byte_range_q_nil Γ dq b off : byte_range_q Γ dq b off [] ⊣⊢ emp.
  Proof. rewrite /byte_range_q //. Qed.

  Lemma byte_range_nil Γ b off : byte_range Γ b off [] ⊣⊢ emp.
  Proof. rewrite /byte_range byte_range_q_nil //. Qed.

  Lemma byte_range_q_app Γ dq b off bs1 bs2 :
    byte_range_q Γ dq b off (bs1 ++ bs2)
    ⊣⊢ byte_range_q Γ dq b off bs1
        ∗ byte_range_q Γ dq b (off + Z.of_nat (length bs1)) bs2.
  Proof.
    rewrite /byte_range_q big_sepL_app.
    apply bi.sep_proper; [done |].
    apply big_sepL_proper. intros k y _.
    assert (Hz : b * BSIZE_z + off + Z.of_nat (length bs1 + k)
                 = b * BSIZE_z + (off + Z.of_nat (length bs1)) + Z.of_nat k)
      by lia.
    rewrite Hz //.
  Qed.

  Lemma byte_range_app Γ b off bs1 bs2 :
    byte_range Γ b off (bs1 ++ bs2)
    ⊣⊢ byte_range Γ b off bs1
        ∗ byte_range Γ b (off + Z.of_nat (length bs1)) bs2.
  Proof. rewrite /byte_range byte_range_q_app //. Qed.

  (* ---------------------------------------------------------------- *)
  (*  2a.  SPLITTING A RUN ALONG [⋅] -- how the quarter is handed out  *)
  (* ---------------------------------------------------------------- *)

  Lemma byte_range_q_split Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) b off bs :
    byte_range_q Γ (DfracOwn (q1 + q2)) b off bs
    ⊣⊢ byte_range_q Γ (DfracOwn q1) b off bs
        ∗ byte_range_q Γ (DfracOwn q2) b off bs.
  Proof.
    rewrite /byte_range_q -big_sepL_sep.
    apply big_sepL_proper. intros k v _. apply Hfr.
  Qed.

  Lemma blk_owned_q_split Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) b bs :
    blk_owned_q Γ (DfracOwn (q1 + q2)) b bs
    ⊣⊢ blk_owned_q Γ (DfracOwn q1) b bs ∗ blk_owned_q Γ (DfracOwn q2) b bs.
  Proof.
    rewrite /blk_owned_q (byte_range_q_split Γ Hfr).
    iSplit.
    - iIntros "[%Hl [H1 H2]]". iSplitL "H1"; by iFrame.
    - iIntros "[[%Hl H1] [_ H2]]". by iFrame.
  Qed.

  (* the shares the design names: a read-locker takes a quarter and the
     escrow keeps three quarters (plan section 4) *)
  Lemma blk_owned_split_34 Γ (Hfr : phi_frac Γ) b bs :
    blk_owned Γ b bs
    ⊣⊢ blk_owned_q Γ (DfracOwn (3/4)) b bs ∗ blk_owned_q Γ (DfracOwn (1/4)) b bs.
  Proof.
    rewrite blk_owned_1 -(blk_owned_q_split Γ Hfr (3/4) (1/4)).
    rewrite Qp.three_quarter_quarter //.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  3.  Exclusivity: two owners of one byte is [False]               *)
  (*                                                                   *)
  (*  This is the ONE exclusivity law the design ever invokes -- used  *)
  (*  exactly as [l ↦ _ ∗ l ↦ _ ⊢ False] is, to learn that two owned   *)
  (*  things are different objects, never as an invariant.             *)
  (* ---------------------------------------------------------------- *)

  (* the general form: two runs at the same address bound their shares *)
  Lemma byte_range_q_valid Γ (Hex : phi_excl Γ) dq1 dq2 b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range_q Γ dq1 b off bs -∗ byte_range_q Γ dq2 b off bs' -∗
    ⌜✓ (dq1 ⋅ dq2)⌝.
  Proof.
    intros Hl Hl'.
    iIntros "H H'".
    destruct (lookup_lt_is_Some_2 bs 0%nat Hl) as [v Hv].
    destruct (lookup_lt_is_Some_2 bs' 0%nat Hl') as [v' Hv'].
    rewrite /byte_range_q.
    iDestruct (big_sepL_lookup _ _ 0%nat v Hv with "H") as "H1".
    iDestruct (big_sepL_lookup _ _ 0%nat v' Hv' with "H'") as "H2".
    iApply (Hex (b * BSIZE_z + off + Z.of_nat 0%nat) v v' dq1 dq2).
    iFrame.
  Qed.

  Lemma byte_range_q_excl Γ (Hex : phi_excl Γ) dq1 dq2 b off bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range_q Γ dq1 b off bs -∗ byte_range_q Γ dq2 b off bs' -∗ False.
  Proof.
    intros Hnv Hl Hl'. iIntros "H H'".
    iDestruct (byte_range_q_valid Γ Hex dq1 dq2 b off bs bs' Hl Hl'
                 with "H H'") as %Hv.
    done.
  Qed.

  (* [DfracOwn 1] excludes ANY other share: the shape every fraction-1
     reading below goes through. *)
  Lemma dfrac_full_nvalid (dq : dfrac) : ~ ✓ (DfracOwn 1 ⋅ dq).
  Proof. intros Hv. exact (exclusive_l (DfracOwn 1) dq Hv). Qed.

  Lemma byte_range_excl Γ (Hex : phi_excl Γ) b off bs bs' :
    (0 < length bs)%nat -> (0 < length bs')%nat ->
    byte_range Γ b off bs -∗ byte_range Γ b off bs' -∗ False.
  Proof.
    intros Hl Hl'. rewrite !byte_range_1.
    iApply (byte_range_q_excl Γ Hex (DfracOwn 1) (DfracOwn 1) b off bs bs'
              (dfrac_full_nvalid _) Hl Hl').
  Qed.

  Lemma BSIZE_pos_nat : (0 < BSIZE)%nat.
  Proof. rewrite /BSIZE. lia. Qed.

  Lemma blk_owned_q_excl Γ (Hex : phi_excl Γ) dq1 dq2 b bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    blk_owned_q Γ dq1 b bs -∗ blk_owned_q Γ dq2 b bs' -∗ False.
  Proof.
    intros Hnv.
    iIntros "[%Hl H] [%Hl' H']".
    iApply (byte_range_q_excl Γ Hex dq1 dq2 b 0 bs bs' Hnv with "H H'");
      [rewrite Hl | rewrite Hl']; apply BSIZE_pos_nat.
  Qed.

  Lemma blk_owned_excl Γ (Hex : phi_excl Γ) b bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b bs' -∗ False.
  Proof.
    rewrite !blk_owned_1.
    iApply (blk_owned_q_excl Γ Hex (DfracOwn 1) (DfracOwn 1) b bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* "distinctness of an inode's own blocks is the [∗]" (fs-state.md
     section 2): the disjointness clause [blkmap_wf]'s injectivity used to
     state is a CONSEQUENCE here, not a maintained fact. *)
  Lemma blk_owned_q_ne Γ (Hex : phi_excl Γ) dq1 dq2 b b' bs bs' :
    ~ ✓ (dq1 ⋅ dq2) ->
    blk_owned_q Γ dq1 b bs -∗ blk_owned_q Γ dq2 b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    intros Hnv.
    iIntros "H H'". destruct (decide (b = b')) as [-> | Hne]; [| done].
    iDestruct (blk_owned_q_excl Γ Hex dq1 dq2 _ _ _ Hnv with "H H'") as "[]".
  Qed.

  Lemma blk_owned_ne Γ (Hex : phi_excl Γ) b b' bs bs' :
    blk_owned Γ b bs -∗ blk_owned Γ b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    rewrite !blk_owned_1.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn 1) (DfracOwn 1) b b' bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* THE TWO SPECIALISATIONS THE DESIGN NAMES (plan section 4).

     [_full]: a full owner excludes ANY other share -- which is what makes
     "a read-locker cannot write a data block" a resource fact, since
     [SpecLogWrite.wp_log_write_au_range] needs fraction 1.
     [_34]: two THREE-QUARTER owners cannot alias, because 3/4 + 3/4 > 1.
     That is the reason the reader's share is a quarter: the commit's
     collection lemma reads cross-inode block disjointness off the [∗]
     between two read-locked inodes' escrow residues. *)
  Lemma blk_owned_ne_full Γ (Hex : phi_excl Γ) dq b b' bs bs' :
    blk_owned Γ b bs -∗ blk_owned_q Γ dq b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    rewrite blk_owned_1.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn 1) dq b b' bs bs'
              (dfrac_full_nvalid _)).
  Qed.

  (* 3/4 + 3/4 > 1 -- the arithmetic that makes the reader's share a
     QUARTER and not a half (plan section 4) *)
  Lemma dfrac_34_nvalid : ~ ✓ (DfracOwn (3/4) ⋅ DfracOwn (3/4)).
  Proof.
    rewrite dfrac_op_own. intros Hv%dfrac_valid_own.
    apply (Qp.lt_nge 1 (3/4 + 3/4)%Qp); [| exact Hv].
    apply Qp.lt_sum. exists (1/2)%Qp. compute_done.
  Qed.

  Lemma blk_owned_ne_34 Γ (Hex : phi_excl Γ) b b' bs bs' :
    blk_owned_q Γ (DfracOwn (3/4)) b bs -∗
    blk_owned_q Γ (DfracOwn (3/4)) b' bs' -∗ ⌜b <> b'⌝.
  Proof.
    iApply (blk_owned_q_ne Γ Hex (DfracOwn (3/4)) (DfracOwn (3/4)) b b' bs bs'
              dfrac_34_nvalid).
  Qed.

End GammaDefs.

Global Arguments fs_view_names : clear implicits.
Global Existing Instance gtimeless.

(* Any [Definition] whose body is a big-op over a block-sized list must be
   sealed the day it is written, or [iFrame] resolves its [Frame] instances
   up to delta, unfolds a 1024-element [big_sepL] and does not come back
   (measured at over ten minutes on the concrete twin, [FsBlocks.fsblock]).
   [rewrite /byte_range] and the declared [Timeless] instances still work. *)
Global Typeclasses Opaque byte_range_q blk_owned_q byte_range blk_owned.
